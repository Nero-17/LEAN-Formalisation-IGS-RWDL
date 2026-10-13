import pathlib, os, subprocess, hashlib, json, datetime, sys
sys.stdout.reconfigure(encoding='utf-8')
root = pathlib.Path(__file__).resolve().parents[1]
repo = root.parent
cache = root / '.lake/corrected-spectrum/lib/lean'
source = root / ('RequestProject/Outlook/' + sys.argv[1] + '.lean')
output = cache / ('RequestProject/Outlook/' + sys.argv[1] + '.olean')
log = root / ('build-logs/' + sys.argv[1] + '.sol-attempt-' + sys.argv[2] + '.log')
compiler = repo.parent / 'elan/toolchains/leanprover--lean4---v4.28.0/bin/lean.exe'
packages = repo / 'section3-diffusion/.lake/packages'
env = os.environ.copy()
env['LEAN_PATH'] = ';'.join([str(cache)] + [str(p / '.lake/build/lib/lean') for p in packages.iterdir() if p.is_dir()])
start = datetime.datetime.now(datetime.timezone.utc).isoformat()
digest = hashlib.sha256(source.read_bytes()).hexdigest().upper()
with log.open('w', encoding='utf-8') as stream:
    stream.write(f'source={source}\nstarted={start}\nsource_sha256={digest}\n')
    stream.flush()
    completed = subprocess.run([str(compiler), '-o', str(output), str(source)], cwd=root, env=env, stdout=stream, stderr=subprocess.STDOUT)
    end = datetime.datetime.now(datetime.timezone.utc).isoformat()
    stream.write(f'exit={completed.returncode}\nfinished={end}\n')
record = dict(source=str(source), source_sha256=digest, current_source_sha256=hashlib.sha256(source.read_bytes()).hexdigest().upper(), logged_start_utc=start, end_utc=end, exit_code=completed.returncode, compiler=str(compiler), log=str(log))
pathlib.Path(str(log) + '.receipt.json').write_text(json.dumps(record, indent=2), encoding='utf-8')
manifest = root / 'build-logs/sol-percolation-verification.json'
records = json.loads(manifest.read_text(encoding='utf-8-sig')) if manifest.exists() else []
if not isinstance(records, list): records = [records]
records.append(record)
manifest.write_text(json.dumps(records, indent=2), encoding='utf-8')
print(log.read_text(encoding='utf-8'), flush=True)
sys.exit(completed.returncode)
