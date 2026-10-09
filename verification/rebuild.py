#!/usr/bin/env python3
"""Rebuild every shipped project module without reusing any project object.

Pinned Mathlib/dependency caches and the pinned Lean installation are allowed.
Run `lake exe cache get` first, or supply --external-package-root locally.
Use a fresh --output directory for each run; no completed evidence is replaced.
The default compiler is resolved by elan in the shipped project.
--preflight-only validates inputs and isolation without compiling a theorem.
"""
from pathlib import Path
import argparse
import concurrent.futures
import datetime
import hashlib
import json
import os
import re
import shutil
import subprocess
import time

DEFAULT_ROOT = Path(__file__).resolve().parents[1]
EXPECTED_LEAN_VERSION = '4.35.0-rc3'
EXPECTED_LEAN_COMMIT = '470d5ce1400764999581fd26d5d72b00d990b0f4'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
def write(p, value):
    q = p.with_suffix(p.suffix+'.tmp')
    q.write_text(json.dumps(value, indent=2)+'\n')
    q.replace(p)
def stamp(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def rel(module): return Path(*module.split('.'))

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--project-root', type=Path, default=DEFAULT_ROOT,
                    help='Shipped source root; defaults to the parent of verification/.')
parser.add_argument('--external-package-root', type=Path,
                    help='Pinned package checkout root; defaults to PROJECT_ROOT/.lake/packages.')
parser.add_argument('--lean',
                    help='Explicit real Lean executable; by default use elan which lean in PROJECT_ROOT.')
parser.add_argument('--expected-compiler-sha256',
                    help='Optional platform-specific compiler binary SHA-256 pin.')
parser.add_argument('--preflight-only', action='store_true',
                    help='Check compiler, source/dependency hashes, and import isolation; compile nothing.')
parser.add_argument('--workers', type=int, default=4)
parser.add_argument('--output', type=Path,
                    help='New evidence directory; defaults to PROJECT_ROOT/verification/clean-build.')
args = parser.parse_args()
ROOT = args.project_root.resolve()
assert 1 <= args.workers <= 4
assert (ROOT/'lean-toolchain').read_text().strip() == 'leanprover/lean4:v'+EXPECTED_LEAN_VERSION
if args.lean is None:
    compiler_selection = 'elan which lean in project root'
    selected = subprocess.check_output(['elan','which','lean'],cwd=ROOT,text=True).strip()
else:
    compiler_selection = 'explicit --lean'
    selected = shutil.which(args.lean) or str(ROOT/args.lean)
lean = Path(selected).resolve()
assert lean.is_file(), ('missing compiler executable',str(lean))
version_output = subprocess.check_output([str(lean),'--version'],cwd=ROOT,text=True).strip()
match = re.search(r'Lean \(version ([^,]+),',version_output)
assert match and match.group(1) == EXPECTED_LEAN_VERSION, ('unexpected Lean version',version_output)
compiler_commit = subprocess.check_output([str(lean),'--githash'],cwd=ROOT,text=True).strip()
assert compiler_commit == EXPECTED_LEAN_COMMIT, ('unexpected Lean commit',compiler_commit)
compiler_hash = sha(lean)
if args.expected_compiler_sha256 is not None:
    expected_hash = args.expected_compiler_sha256.lower()
    assert re.fullmatch(r'[0-9a-f]{64}',expected_hash), 'Expected compiler SHA-256 must be 64 hexadecimal characters.'
    assert compiler_hash == expected_hash, ('compiler binary hash mismatch',compiler_hash,expected_hash)
else:
    expected_hash = None
stdlib = lean.parent.parent/'lib/lean'
assert stdlib.is_dir(), ('missing compiler standard library; supply a real executable rather than an elan proxy',str(stdlib))
args.external_package_root = (args.external_package_root or ROOT/'.lake/packages').resolve()
OUT = (args.output or ROOT/'verification/clean-build').resolve()
assert not OUT.exists(), 'Use a new output directory; preserve prior build evidence.'
OUT.mkdir(parents=True)
LIB = OUT/'project-objects'
LOGS = OUT/'logs'
LIB.mkdir(); LOGS.mkdir()
manifest = json.loads((ROOT/'verification/source-manifest.json').read_text())
sources = manifest['source_provenance']
assert len(sources) == manifest['source_modules']
for module, e in sources.items():
    assert sha(ROOT/rel(module).with_suffix('.lean')) == e['source_sha256'], module

packages = json.loads((ROOT/'lake-manifest.json').read_text())['packages']
external_paths, pins = [], []
for e in packages:
    p = (args.external_package_root/e['name']).resolve()
    revision = subprocess.check_output(['git','rev-parse','HEAD'], cwd=p, text=True).strip()
    assert revision == e['rev'], (e['name'], revision, e['rev'])
    dirty = subprocess.check_output(['git','status','--porcelain','--untracked-files=no'], cwd=p, text=True)
    assert not dirty.strip(), ('modified pinned dependency', e['name'])
    lib = p/'.lake/build/lib/lean'
    if lib.is_dir(): external_paths.append(lib)
    pins.append(dict(name=e['name'], revision=revision, object_cache_present=lib.is_dir()))
external_paths.append(stdlib)
external_hashes = {}
for module in manifest['external_imports']:
    p = next((d/rel(module).with_suffix('.olean') for d in external_paths
              if (d/rel(module).with_suffix('.olean')).is_file()), None)
    assert p is not None, ('missing external object', module)
    external_hashes[module] = dict(object_sha256=sha(p), location=str(p))
assert not any(LIB.rglob('*.olean'))
env = dict(os.environ)
env.update(LEAN_PATH=os.pathsep.join(map(str,[LIB,*external_paths])),
           LEAN_NUM_THREADS='1', OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1')
flags = ['-j1','-M12288','-t0','-DmaxSynthPendingDepth=3']
preflight = dict(status='PREFLIGHT_PASS' if args.preflight_only else 'RUNNING',
                 started_utc=stamp(), source_modules=len(sources),
                 preflight_only=args.preflight_only, compilation_started=False,
                 project_objects_reused=False, full_project_source_rebuild=not args.preflight_only,
                 external_mathlib_sources_rebuilt=False, dependency_pins=pins,
                 compiler_sha256=compiler_hash, compiler_version=EXPECTED_LEAN_VERSION,
                 compiler_commit=compiler_commit, compiler_version_output=version_output,
                 compiler_path=str(lean), compiler_selection=compiler_selection,
                 expected_compiler_sha256=expected_hash,
                 launcher_sha256=sha(Path(__file__)), flags=flags, workers=args.workers,
                 LEAN_PATH=env['LEAN_PATH'].split(os.pathsep),
                 external_direct_imports=external_hashes,
                 source_manifest_sha256=sha(ROOT/'verification/source-manifest.json'))
write(OUT/'preflight.json',preflight)
if args.preflight_only:
    receipt = dict(status='PREFLIGHT_PASS',preflight_passed=True,
                   full_project_source_rebuild=False,project_objects_reused=False,
                   compilation_started=False,source_modules=len(sources),rebuilt_modules=0,
                   endpoint_audit=None,finished_utc=stamp(),
                   compiler_version=EXPECTED_LEAN_VERSION,compiler_commit=compiler_commit,
                   compiler_sha256=compiler_hash,expected_compiler_sha256=expected_hash,
                   launcher_sha256=sha(Path(__file__)),
                   preflight_sha256=sha(OUT/'preflight.json'))
    write(OUT/'receipt.json',receipt)
    write(OUT/'progress.json',dict(status='PREFLIGHT_PASS',completed=0,total=len(sources),
          compilation_started=False,receipt_sha256=sha(OUT/'receipt.json')))
    print(json.dumps(receipt),flush=True)
    raise SystemExit(0)
dependencies = {m:set(e['imports'])&set(sources) for m,e in sources.items()}
pending, done, running, results = set(sources), set(), {}, []
started = time.monotonic()
def compile_one(module):
    source = ROOT/rel(module).with_suffix('.lean')
    target = LIB/rel(module).with_suffix('.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    command = [str(lean),*flags,'-o',str(target),str(source)]
    before = sha(source)
    t = time.monotonic()
    run = subprocess.run(command, env=env, cwd=ROOT, capture_output=True, text=True)
    log = LOGS/(module+'.log')
    log.write_text(run.stdout+run.stderr)
    entry = dict(module=module, exit_status=run.returncode, seconds=time.monotonic()-t,
                 source_sha256=before, source_unchanged=sha(source)==before,
                 log_sha256=sha(log), warning_count=(run.stdout+run.stderr).count('warning:'),
                 sorry_axiom_in_log='sorryAx' in run.stdout+run.stderr)
    if target.exists(): entry['object_sha256']=sha(target)
    return entry
failed = False
with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
    while pending or running:
        ready = sorted(m for m in pending if dependencies[m]<=done)
        for m in ready[:args.workers-len(running)]:
            pending.remove(m)
            running[pool.submit(compile_one,m)] = m
        assert running, ('dependency cycle',sorted(pending))
        completed, _ = concurrent.futures.wait(running,
                            return_when=concurrent.futures.FIRST_COMPLETED)
        for f in completed:
            m = running.pop(f)
            e = f.result(); results.append(e)
            ok = e['exit_status']==0 and e['source_unchanged'] and not e['sorry_axiom_in_log']
            if ok: done.add(m)
            else: failed=True
            print(f'{len(done)}/{len(sources)} {m}: {"PASS" if ok else "FAIL"}', flush=True)
            write(OUT/'progress.json',dict(status='FAILED' if failed else 'RUNNING',
                checked_at_utc=stamp(), completed=len(done), total=len(sources),
                elapsed_seconds=time.monotonic()-started, running=sorted(running.values()),
                pending=len(pending), results=results))
        if failed:
            for f,m in list(running.items()):
                e=f.result();results.append(e)
            break

audit = None
if not failed:
    audit_source = OUT/'EndpointAudit.lean'
    names = ['poincare15_mem','poincare15','universalPoincareUpper15','openaiPoincare15','openaiKLS']
    audit_source.write_text('import Challenge\n'+''.join(
        '#check KLS15.'+n+'\n#print axioms KLS15.'+n+'\n' for n in names))
    t=time.monotonic()
    run=subprocess.run([str(lean),*flags,str(audit_source)],env=env,cwd=ROOT,
                       capture_output=True,text=True)
    log=run.stdout+run.stderr
    (OUT/'EndpointAudit.log').write_text(log)
    blocks=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log,re.S)
    axioms={a.strip() for b in blocks for a in b.split(',') if a.strip()}
    audit=dict(exit_status=run.returncode,seconds=time.monotonic()-t,
               declaration_queries=len(names),nonempty_axiom_reports=len(blocks),
               axiom_names=sorted(axioms),unexpected_axioms=sorted(axioms-{
                   'propext','Classical.choice','Quot.sound'}),
               source_sha256=sha(audit_source),log_sha256=sha(OUT/'EndpointAudit.log'))
    failed=run.returncode!=0 or len(blocks)!=len(names) or bool(audit['unexpected_axioms'])
for module,e in sources.items():
    assert sha(ROOT/rel(module).with_suffix('.lean'))==e['source_sha256'],module
receipt=dict(status='PASS' if not failed else 'FAIL',all_passed=not failed,
             finished_utc=stamp(),elapsed_seconds=time.monotonic()-started,
             source_modules=len(sources),rebuilt_modules=len(done),
             full_project_source_rebuild=True,project_objects_reused=False,
             external_mathlib_sources_rebuilt=False,compiler_sha256=compiler_hash,
             compiler_version=EXPECTED_LEAN_VERSION,compiler_commit=compiler_commit,
             compiler_version_output=version_output,expected_compiler_sha256=expected_hash,
             launcher_sha256=sha(Path(__file__)),
             preflight_sha256=sha(OUT/'preflight.json'),results=results,
             warning_count=sum(e['warning_count'] for e in results),endpoint_audit=audit)
write(OUT/'receipt.json',receipt)
write(OUT/'progress.json',dict(status=receipt['status'],completed=len(done),total=len(sources),
      checked_at_utc=stamp(),receipt_sha256=sha(OUT/'receipt.json')))
print(json.dumps({k:v for k,v in receipt.items() if k not in ['results']}),flush=True)
raise SystemExit(0 if not failed else 1)
