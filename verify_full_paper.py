"""Verify a hash-identified combined snapshot of the three Lean projects.

This checks integration and kernel acceptance. It does not certify that the
statements discharge every mathematical hypothesis of the paper.
Generated sources, oleans and logs stay under the ignored root .lake directory.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time

repository = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--lean', required=True, type=Path)
parser.add_argument('--targets', nargs='*')
arguments = parser.parse_args()
workspace = repository / '.lake' / 'full-paper-verification'
source_root = workspace / 'src'
build_root = workspace / 'lib' / 'lean'
log_root = workspace / 'logs'
for directory in [source_root, build_root, log_root]:
    directory.mkdir(parents=True, exist_ok=True)
projects = ['section2-random-walks', 'section3-diffusion', 'section4-percolation']
modules = {}
manifest = {}
for project in projects:
    project_root = repository / project
    for path in sorted((project_root / 'RequestProject').rglob('*.lean')):
        relative = path.relative_to(project_root)
        if relative.as_posix() == 'RequestProject/Main.lean':
            continue  # Each old Main contains only imports/options, no declarations.
        module = '.'.join(relative.with_suffix('').parts)
        content = path.read_bytes()
        if module in modules and modules[module][1] != content:
            raise RuntimeError(f'Conflicting modules: {module}')
        modules[module] = (path, content)
        manifest[path.relative_to(repository).as_posix()] = hashlib.sha256(content).hexdigest()
        destination = source_root / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        if not destination.exists() or destination.read_bytes() != content:
            destination.write_bytes(content)

dependencies = {}
for module, (path, content) in modules.items():
    imported = []
    for line in content.decode('utf-8-sig').splitlines():
        match = re.match(r'\s*import\s+(.+)', line)
        if match:
            imported += re.findall(r'\bRequestProject(?:\.[A-Za-z0-9_]+)+', match[1].split('--')[0])
    missing = [name for name in imported if name not in modules]
    if missing:
        raise RuntimeError(f'{module}: missing source dependencies {missing}')
    dependencies[module] = imported
ordered = []
visited = set()
visiting = set()
def visit(module):
    if module in visited:
        return
    if module in visiting:
        raise RuntimeError(f'Import cycle at {module}')
    if module not in modules:
        raise RuntimeError(f'Unknown target {module}')
    visiting.add(module)
    for dependency in dependencies[module]:
        visit(dependency)
    visiting.remove(module)
    visited.add(module)
    ordered.append(module)
for target in arguments.targets or sorted(modules):
    visit(target)

package_root = repository / 'section3-diffusion' / '.lake' / 'packages'
environment = os.environ.copy()
environment['LEAN_PATH'] = os.pathsep.join([str(build_root)] +
    [str(package / '.lake/build/lib/lean') for package in sorted(package_root.iterdir()) if package.is_dir()])
state_path = workspace / 'verification_state.json'
try:
    state = json.loads(state_path.read_text(encoding='utf-8'))
except FileNotFoundError:
    state = {}
version = subprocess.run([str(arguments.lean), '--version'], capture_output=True, text=True, check=True).stdout.strip()
fingerprints = {}
started = time.time()
for position, module in enumerate(ordered, 1):
    path, content = modules[module]
    fingerprint = hashlib.sha256(content + version.encode() +
        '8f9d9cff6bd728b17a24e163c9402775d9e6a365'.encode() +
        ''.join(fingerprints[name] for name in dependencies[module]).encode()).hexdigest()
    fingerprints[module] = fingerprint
    relative = Path(*module.split('.'))
    output = (build_root / relative).with_suffix('.olean')
    log = (log_root / relative).with_suffix('.log')
    if output.exists() and state.get(module, {}).get('fingerprint') == fingerprint:
        print(f'[{position}/{len(ordered)}] cached {module}', flush=True)
        continue
    output.parent.mkdir(parents=True, exist_ok=True)
    log.parent.mkdir(parents=True, exist_ok=True)
    print(f'[{position}/{len(ordered)}] checking {module}', flush=True)
    with log.open('wb') as handle:
        result = subprocess.run([str(arguments.lean), '-o', str(output), str((source_root / relative).with_suffix('.lean'))],
                                env=environment, cwd=source_root, stdout=handle, stderr=subprocess.STDOUT)
    if result.returncode:
        print(log.read_text(encoding='utf-8', errors='replace'), flush=True)
        raise SystemExit(result.returncode)
    state[module] = {'fingerprint': fingerprint, 'source': path.relative_to(repository).as_posix(),
                     'source_sha256': hashlib.sha256(content).hexdigest(), 'verified_unix_time': time.time()}
    state_path.write_text(json.dumps(state, indent=2), encoding='utf-8')
verified_sources = {modules[module][0].relative_to(repository).as_posix() for module in ordered}
changed = [name for name, digest in manifest.items() if name in verified_sources
           if not (repository / name).exists() or hashlib.sha256((repository / name).read_bytes()).hexdigest() != digest]
report = {'compiler': version, 'mathlib': '8f9d9cff6bd728b17a24e163c9402775d9e6a365',
          'targets': arguments.targets, 'verified_modules': ordered, 'snapshot_source_sha256': manifest,
          'verified_source_files': sorted(verified_sources),
          'changed_during_verification': changed, 'elapsed_seconds': time.time() - started,
          'mathematical_scope': 'Kernel acceptance and module integration only; hypothesis closure audited separately.'}
(workspace / 'verification_report.json').write_text(json.dumps(report, indent=2), encoding='utf-8')
print(json.dumps({'verified_modules': len(ordered), 'changed_during_verification': changed,
                  'elapsed_seconds': report['elapsed_seconds']}), flush=True)
if changed:
    raise SystemExit('Canonical sources changed during verification; rerun to verify the current snapshot.')
