"""Run the three finite-check suites into one new output directory.

Usage (from any directory):
    python -B run_all.py --output-dir NEW_OR_EMPTY_DIRECTORY

Without --output-dir a new system temporary directory is used. The runner
refuses a nonempty output directory and never writes inside the suite folders.
It writes one log per check, the suites' own result files, and summary.json,
and exits with status 0 only if every check passes.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
SPATIAL = HERE / 'spatial'
TYPES = HERE / 'types'
ZERO = HERE / 'zero-error'
SUITES = (SPATIAL, TYPES, ZERO)


def parse_args() -> Path:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--output-dir', '-o', type=Path, default=None,
                        help='new or empty directory for all outputs (default: a new temporary directory)')
    args = parser.parse_args()
    out = args.output_dir.resolve() if args.output_dir else Path(tempfile.mkdtemp(prefix='perfect-play-checks-')).resolve()
    for suite in SUITES:
        if out == suite or suite in out.parents:
            parser.error('choose an output directory outside the suite folders')
    if out.exists() and any(out.iterdir()):
        parser.error('output directory must be new or empty')
    out.mkdir(parents=True, exist_ok=True)
    return out


def stable(value):
    """Drop timing and memory telemetry before comparing result files."""
    if isinstance(value, dict):
        return {k: stable(v) for k, v in value.items() if k not in ('elapsed_seconds', 'peak_working_set_bytes')}
    if isinstance(value, list):
        return [stable(v) for v in value]
    return value


def main() -> int:
    out = parse_args()
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1', PYTHONIOENCODING='utf-8',
               OPENBLAS_NUM_THREADS='1', OMP_NUM_THREADS='1', MKL_NUM_THREADS='1')
    results = []

    def run(name: str, argv: list, cwd: Path) -> bool:
        start = time.monotonic()
        proc = subprocess.run([sys.executable, '-B', *map(str, argv)], cwd=cwd, env=env,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, encoding='utf-8')
        log = out / 'logs' / (name + '.log')
        log.parent.mkdir(parents=True, exist_ok=True)
        log.write_text(proc.stdout, encoding='utf-8', newline='\n')
        ok = proc.returncode == 0
        results.append({'check': name, 'exit_code': proc.returncode, 'passed': ok,
                        'seconds': round(time.monotonic() - start, 1)})
        print(('PASS' if ok else 'FAIL') + ': ' + name, flush=True)
        if not ok:
            print(proc.stdout[-3000:], flush=True)
        return ok

    def record(name: str, ok: bool, detail: str) -> None:
        results.append({'check': name, 'passed': ok, 'detail': detail})
        print(('PASS' if ok else 'FAIL') + ': ' + name + ' (' + detail + ')', flush=True)

    # Spatial suite: tree, clock and compiler checks.
    comp = out / 'spatial' / 'compiler'
    run('spatial-good-root', [SPATIAL / 'review' / 'check_good_root.py'], SPATIAL)
    run('spatial-tree-clock', [SPATIAL / 'review' / 'check_tree_clock.py'], SPATIAL)
    run('spatial-exact-audit', [SPATIAL / 'compiler' / 'exact_audit.py', '--output-dir', comp], SPATIAL)
    if run('spatial-minimal-compile', [SPATIAL / 'compiler' / 'minimal_compile.py', '--output-dir', comp], SPATIAL):
        run('spatial-minimal-structural', [SPATIAL / 'compiler' / 'minimal_structural.py', '--output-dir', comp], SPATIAL)
    for name in ('exact_results.json', 'minimal_results.json', 'minimal_structural_results.json'):
        fresh = comp / name
        same = fresh.is_file() and stable(json.loads(fresh.read_text(encoding='utf-8'))) == \
            stable(json.loads((SPATIAL / 'compiler' / name).read_text(encoding='utf-8')))
        record('spatial-compare-' + name, same, 'fresh result equals the shipped result, ignoring telemetry')
    toy = out / 'spatial' / 'toy'
    if run('spatial-toy-table', [SPATIAL / 'review' / 'generate_toy.py', '--output-dir', toy], SPATIAL):
        paper = HERE.parent / 'paper' / 'sections' / 'toy-table.tex'
        if not paper.is_file(): paper = HERE / 'toy-table-expected.tex'
        if paper.is_file():
            gen = (toy / 'toy-table.tex').read_text(encoding='utf-8').splitlines()
            ref = paper.read_text(encoding='utf-8').splitlines()
            # The paper sets the automaton symbols in typewriter; only the column specification differs.
            same = len(gen) == len(ref) and all(a == b for i, (a, b) in enumerate(zip(gen, ref)) if i != 2)
            record('spatial-toy-table-matches-paper', same, 'generated tableau equals paper table apart from the column specification')

    # Type-language suite.
    run('types-check-type-ladder', [TYPES / 'check_type_ladder.py', '--output-dir', out / 'types'], out)

    # Zero-error suite (its runner creates its own fresh directory).
    run('zero-error-run-all', [ZERO / 'run_all.py', '--output-directory', out / 'zero-error'], ZERO)

    # Keep the outputs portable: replace machine-specific absolute paths by placeholders.
    marks = []
    for path, label in ((out, '<output-dir>'), (HERE, '<verification>')):
        for form in (str(path), path.as_posix()):
            marks += [(form, label), (json.dumps(form)[1:-1], label)]
    marks.sort(key=lambda m: -len(m[0]))
    for f in out.rglob('*'):
        if f.is_file() and f.suffix in ('.log', '.json', '.txt', '.out', '.tex'):
            text = f.read_text(encoding='utf-8', errors='strict')
            new = text
            for old, label in marks:
                new = new.replace(old, label)
            if new != text:
                f.write_text(new, encoding='utf-8', newline='\n')

    shipped = sorted(p for suite in SUITES for p in suite.rglob('*') if p.is_file() and '__pycache__' not in p.parts)
    summary = {
        'passed': all(r['passed'] for r in results),
        'python': platform.python_version(),
        'platform': platform.system(),
        'checks': results,
        'suite_files_sha256': {p.relative_to(HERE).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest() for p in shipped},
    }
    try:
        import importlib.metadata as md
        summary['dependencies'] = {m: md.version(m) for m in ('numpy', 'networkx', 'sympy', 'mpmath')}
    except Exception as exc:  # pragma: no cover - reported, not fatal
        summary['dependencies'] = 'unavailable: ' + type(exc).__name__
    (out / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n', encoding='utf-8', newline='\n')
    print('Results: ' + str(out), flush=True)
    return 0 if summary['passed'] else 1


if __name__ == '__main__':
    sys.exit(main())
