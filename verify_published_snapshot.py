"""Check portable evidence hashes; optionally recompile the recorded targets.

Hash checks are not a fresh Lean build or proof of full-paper coverage.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rebuild', action='store_true')
    parser.add_argument('--lean', type=Path)
    parser.add_argument('--evidence', type=Path, default=Path('verification/20261016T024228Z'),
                        help='Evidence directory corresponding to the checked-out source snapshot.')
    arguments = parser.parse_args()
    repository = Path(__file__).resolve().parent
    evidence = repository / arguments.evidence
    manifest = json.loads((evidence / 'accepted-receipts.json').read_text(encoding='utf-8'))
    statuses = json.loads((evidence / 'source-status.json').read_text(encoding='utf-8'))
    listed_sources = {record['source'] for record in statuses}
    actual_sources = {
        source.relative_to(repository).as_posix()
        for project in ['section2-random-walks', 'section3-diffusion', 'section4-percolation']
        for source in (repository / project / 'RequestProject').rglob('*.lean')
    }
    if listed_sources != actual_sources or len(listed_sources) != len(statuses):
        raise ValueError('The source-status inventory is incomplete or contains duplicates')
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}

    def check_hash(path, expected):
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError(f'SHA256 mismatch: {path.relative_to(repository)}')

    integration_path = evidence / manifest['shared_report']
    check_hash(integration_path, manifest['shared_report_sha256'])
    integration = json.loads(integration_path.read_text(encoding='utf-8'))
    if (integration['changed_during_verification'] or
            len(integration['verified_modules']) != manifest['shared_dependency_modules']):
        raise ValueError('The published shared-dependency report is not the recorded passing batch')
    for name in integration['verified_source_files']:
        check_hash(repository / name, integration['snapshot_source_sha256'][name])
    for status in statuses:
        check_hash(repository / status['source'], status['source_sha256'])
    for record in manifest['records']:
        if record['exit_code'] != 0:
            raise ValueError('Nonzero accepted receipt')
        check_hash(repository / record['source'], record['source_sha256'])
        log = evidence / record['log']
        check_hash(log, record['log_sha256'])
        content = log.read_text(encoding='utf-8')
        actual_audits = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", content, re.S)
        if not actual_audits or 'sorryAx' in content or 'error:' in content:
            raise ValueError('An accepted log contains a failure or no printed audits')
        normalized = [{'declaration': name, 'axioms': [a.strip() for a in axioms.split(',') if a.strip()]}
                      for name, axioms in actual_audits]
        if normalized != record['audits']:
            raise ValueError('Printed audit declarations differ from the manifest')
        if any(not set(audit['axioms']) <= allowed for audit in normalized):
            raise ValueError('An audit uses an unapproved axiom')
    targets = (evidence / 'verified-targets.txt').read_text(encoding='utf-8').splitlines()
    print(json.dumps({'hash_checks': 'passed', 'shared_modules': manifest['shared_dependency_modules'],
        'independent_whole_files': len(manifest['records']), 'source_files': len(statuses),
        'note': 'Receipt verification only; full-paper completion is not claimed.'}))
    if arguments.rebuild:
        if not arguments.lean:
            parser.error('--rebuild requires --lean')
        subprocess.run([sys.executable, str(repository / 'verify_full_paper.py'),
            '--lean', str(arguments.lean), '--targets-file', str(evidence / 'verified-targets.txt')], check=True)


if __name__ == '__main__':
    main()
