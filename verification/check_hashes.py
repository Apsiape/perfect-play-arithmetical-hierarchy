"""Check SHA256SUMS: LF line endings, relative paths, and every listed hash.

It also reports files present in this directory but missing from the list.
Usage: python -B check_hashes.py
"""
from pathlib import Path, PurePosixPath
import hashlib
import sys

HERE = Path(__file__).resolve().parent
SKIP_DIRS = {'__pycache__', 'generated'}


def main() -> int:
    raw = (HERE / 'SHA256SUMS').read_bytes()
    if b'\r' in raw or not raw.endswith(b'\n'):
        print('FAIL: SHA256SUMS must use LF line endings')
        return 1
    listed, failed = set(), []
    for line in raw.decode('utf-8').splitlines():
        digest, name = line.split('  ', 1)
        rel = PurePosixPath(name)
        if rel.is_absolute() or '..' in rel.parts or ':' in name or '\\' in name:
            failed.append(name)
            continue
        listed.add(name)
        path = HERE / name
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            failed.append(name)
    present = {p.relative_to(HERE).as_posix() for p in HERE.rglob('*')
               if p.is_file() and not SKIP_DIRS & set(p.relative_to(HERE).parts)}
    unlisted = sorted(present - listed - {'SHA256SUMS'})
    if failed or unlisted:
        if failed:
            print('FAIL: hash mismatch or bad path: ' + ', '.join(sorted(failed)))
        if unlisted:
            print('FAIL: not listed: ' + ', '.join(unlisted))
        return 1
    print(f'PASS: {len(listed)} files match SHA256SUMS; LF line endings; no unlisted files')
    return 0


if __name__ == '__main__':
    sys.exit(main())
