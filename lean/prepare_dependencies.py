"""Copy exact pinned local dependency sources into vendor/, without Git or build objects."""
from pathlib import Path
import argparse,hashlib,json,shutil
ROOT=Path(__file__).resolve().parent
ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--source-dir',required=True,type=Path);ap.add_argument('--check-only',action='store_true');a=ap.parse_args()
source=a.source_dir.resolve();target=ROOT/'vendor';assert source!=target.resolve(),'Choose an external read-only source cache'
entries=json.loads((ROOT/'pins/DEPENDENCY-SOURCES.json').read_text(encoding='utf-8'))['files']
overrides={'mathlib/Cache/Requests.lean': ROOT/'cache-tool/Requests.lean'}
for entry in entries:
 rel=Path(entry['path']);assert not rel.is_absolute() and '..' not in rel.parts
 p=overrides.get(entry['path'],source/rel);assert p.is_file(),'Missing dependency source: '+str(rel)
 with p.open('rb') as f:digest=hashlib.file_digest(f,'sha256').hexdigest()
 assert digest==entry['sha256'],'Wrong dependency source: '+str(rel)
if a.check_only:
 print('Verified',len(entries),'exact dependency sources including the one bundled cache-tool override.');raise SystemExit(0)
for entry in entries:
 rel=Path(entry['path']);q=target/rel;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(overrides.get(entry['path'],source/rel),q)
print('Verified and copied',len(entries),'source files. Next: lake exe cache get; lake build')
