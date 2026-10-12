#!/usr/bin/env python3
"""Scoped, local BKL source-target checks; baseline changes are explicit and reviewed."""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
sys.path.insert(0, str(ROOT / 'research'))
import statement_snapshot
import verify


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def specification_guard(source):
    imports = re.findall(r'^(?:public )?import\s+(\S+)', source, re.M)
    if not imports or any(not name.startswith('Mathlib.') for name in imports):
        raise ValueError('Standalone specification must import Mathlib only')
    if re.search(r'\b(?:FunctionalInequalities|Solutions|sorry|axiom)\b', source):
        raise ValueError('Standalone specification contains a project target or placeholder')
    return imports


def rejected_mutation(output, kind):
    reasons = {'factorial': 'unsolved goals', 'coefficient': 'Type mismatch',
               'dimension': 'Application type mismatch'}
    return bool(re.search(r'BKLIndependentChecks\.lean:\d+:\d+: error: ' + reasons[kind], output))


def module_source(name):
    if name == 'FunctionalInequalities':
        return ROOT / 'formalization/FunctionalInequalities.lean'
    if name.startswith('FunctionalInequalities.'):
        return ROOT / 'formalization' / (name.replace('.', '/') + '.lean')
    if name.startswith(('solutions.', 'examples.')):
        return ROOT / (name.replace('.', '/') + '.lean')
    return None


def closure(modules):
    found = {}
    pending = list(modules)
    while pending:
        name = pending.pop()
        if name in found:
            continue
        source = module_source(name)
        if source is None:
            continue
        if not source.is_file():
            raise ValueError('Missing local import source: ' + name)
        found[name] = source
        pending += re.findall(r'^(?:public )?import\s+(\S+)', source.read_text(), re.M)
    return dict(sorted(found.items()))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['check', 'baseline'])
    parser.add_argument('--paper', type=Path, required=True, help='Pinned v1 PDF, hash checked')
    parser.add_argument('--mutations', action='store_true', help='Run three rejecting Lean mutations')
    args = parser.parse_args()
    config = json.loads((HERE / 'config.json').read_text())
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    output = ROOT / 'build/reviews/2026-10-12-bkl-independent-targets/runs' / stamp
    output.mkdir(parents=True)
    report = {'version': 1, 'status': 'failed', 'scope': 'BKL independent source-target pilot',
              'stages': [], 'errors': [], 'output': str(output.relative_to(ROOT)),
              'trust_scope': 'Source-build of the certificate import closure; independent Mathlib-only specification; '
              'explicit definition bridges and standard axiom audit; replay of two certificates and two audit modules. '
              'Pinned Mathlib/third-party compiled imports are trusted. No second kernel or full-library verification.'}
    env = {**os.environ, 'GIT_OPTIONAL_LOCKS': '0', 'LEAN_NUM_THREADS': '2'}
    env.pop('LEAN_PATH', None)
    formalization = ROOT / 'formalization'

    def run(stage, command, *, input=None, run_env=None, expected_failure=False):
        print('Checking ' + stage + '...', flush=True)
        start = time.monotonic()
        result = subprocess.run(command, cwd=formalization, env=run_env or env, input=input,
                                text=True, capture_output=True)
        log = output / (stage + '.log')
        log.write_text(result.stdout + result.stderr)
        report['stages'].append({'name': stage, 'exit_code': result.returncode,
                                'seconds': round(time.monotonic() - start, 3), 'log': str(log.relative_to(ROOT)),
                                'log_sha256': sha(log), 'expected_failure': expected_failure})
        if (expected_failure and result.returncode == 0) or (not expected_failure and result.returncode):
            raise RuntimeError(stage + ' failed its acceptance condition; see ' + str(log.relative_to(ROOT)))
        return result.stdout

    try:
        if sha(args.paper) != config['paper']['pdf_sha256']:
            raise ValueError('PDF does not match pinned BKL v1')
        report['paper'] = {**config['paper'], 'checked_path': str(args.paper.resolve())}
        spec = (HERE / 'Specification.lean.in').read_text()
        report['specification_imports'] = specification_guard(spec)
        if re.search(r'\b(?:sorry|axiom)\b', (HERE / 'Checks.lean.in').read_text()):
            raise ValueError('Audit link contains a placeholder or project axiom')
        modules = closure(config['certificate_modules'])
        scope_files = [*modules.values(), *sorted(HERE.glob('*')),
                       ROOT / 'research/StatementSnapshot.lean', ROOT / 'research/statement_snapshot.py',
                       ROOT / 'research/verify.py', ROOT / config['review'],
                       formalization / 'lean-toolchain', formalization / 'lakefile.toml',
                       formalization / 'lake-manifest.json']
        scope_files = [p for p in scope_files if p.is_file() and p.name != config['baseline']]
        before = {str(p.relative_to(ROOT)): sha(p) for p in scope_files}
        report['source_identity'] = {'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, env=env, text=True).strip(),
                                     'files': before, 'sha256': hashlib.sha256(json.dumps(before, sort_keys=True).encode()).hexdigest()}
        report['built_local_modules'] = list(modules)
        run('certificate-build', ['lake', 'build', *('+' + m for m in config['certificate_modules'])])
        prefix = run('toolchain-prefix', ['lake', 'env', 'lean', '--print-prefix']).strip()
        report['compiler_githash'] = run('compiler-githash', [prefix + '/bin/lean', '--githash']).strip()
        search = run('package-search-path', ['lake', 'env', 'printenv', 'LEAN_PATH']).strip().split(os.pathsep)
        view = output / 'local-olean'
        view.mkdir()
        compiled = formalization / '.lake/build/lib/lean'
        artifacts = {}
        for name in modules:
            relative = Path(name.replace('.', '/'))
            for suffix in ['.olean', '.olean.private', '.olean.server', '.ir']:
                source = compiled / relative.with_suffix(suffix)
                if not source.exists():
                    if suffix == '.olean':
                        raise ValueError('Missing rebuilt artifact: ' + name)
                    continue
                destination = view / source.relative_to(compiled)
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(source, destination)
                artifacts[str(destination.relative_to(view))] = sha(destination)
        report['rebuilt_artifact_hashes'] = artifacts
        paths = [str((formalization / p).resolve()) for p in search]
        matches = [i for i, p in enumerate(paths) if Path(p) == compiled.resolve()]
        if len(matches) != 1:
            raise ValueError('Expected exactly one local package search path')
        paths[matches[0]] = str(view)
        runtime = output / 'runtime'
        runtime.mkdir()
        lean_env = {**env, 'LEAN_PATH': os.pathsep.join([str(runtime), *paths])}
        lean = prefix + '/bin/lean'
        for name, template in [('BKLIndependentSpecification', 'Specification.lean.in'),
                               ('BKLIndependentChecks', 'Checks.lean.in')]:
            source = runtime / (name + '.lean')
            source.write_bytes((HERE / template).read_bytes())
            result = run(name, [lean, '-DwarningAsError=true', '-R', str(runtime), '-o',
                                str(runtime / (name + '.olean')), str(source)], run_env=lean_env)
            if name.endswith('Checks'):
                expected = {'BKLIndependentChecks.' + n for n in config['checks']}
                axioms, errors = verify.parse_axioms(result, expected)
                if errors:
                    raise ValueError('; '.join(errors))
                report['axioms'] = axioms
        inspection = 'import BKLIndependentChecks\n' + (ROOT / 'research/StatementSnapshot.lean').read_text()
        inspection += '\n#statement_snapshot_owned ' + ' '.join(config['owners']) + ' => ' + ' '.join(config['roots']) + '\n'
        (output / 'Inspection.lean').write_text(inspection)
        result = run('statement-closure', [lean, '-DwarningAsError=true', '--stdin'], input=inspection, run_env=lean_env)
        current = json.loads(result)
        if current['roots'] != config['roots'] or not current['declarations']:
            raise ValueError('Missing target/type definition closure')
        current = {'version': 1, 'toolchain': (formalization / 'lean-toolchain').read_text().strip(),
                   'lake_manifest_sha256': sha(formalization / 'lake-manifest.json'),
                   'printing': {'pp.all': True, 'pp.proofs': True, 'pp.maxSteps': 1000000, 'width': 100}, **current}
        (output / 'statement-closure.json').write_text(json.dumps(current, indent=2, ensure_ascii=False) + '\n')
        decision = statement_snapshot.decision_record(ROOT, config['review'])
        golden = HERE / config['baseline']
        if args.command == 'baseline':
            if golden.exists():
                raise ValueError('Pilot baseline already exists; a new reviewed baseline must be established separately')
            pending_golden = json.dumps({**current, 'decision': decision}, indent=2, ensure_ascii=False) + '\n'
            report['baseline_action'] = 'created explicitly after source review'
        else:
            if not golden.is_file():
                raise ValueError('Missing reviewed pilot baseline')
            previous = json.loads(golden.read_text())
            if previous['decision'] != decision:
                raise ValueError('Source-review record changed; do not silently refresh the baseline')
            errors = statement_snapshot.compare_snapshot(current, previous)
            if errors:
                raise ValueError('; '.join(errors))
            report['baseline_action'] = 'matched; not refreshed'
        report['statement_closure'] = {'roots': len(current['roots']), 'local_declarations': len(current['declarations']),
                                       'external_leaves': len(current['external']), 'golden_sha256': sha(golden) if golden.exists() else hashlib.sha256(pending_golden.encode()).hexdigest()}
        replay = run('kernel-replay', [prefix + '/bin/leanchecker', '--verbose',
                     *config['certificate_modules'], 'BKLIndependentSpecification', 'BKLIndependentChecks'], run_env=lean_env)
        replayed = sorted(set(re.findall(r'(?m)^replaying (\S+)\s*$', replay)))
        expected_modules = sorted([*config['certificate_modules'], 'BKLIndependentSpecification', 'BKLIndependentChecks'])
        if replayed != expected_modules:
            raise ValueError('Kernel replay coverage differs from the four requested modules')
        report['replayed_modules'] = replayed
        if args.mutations:
            mutations = {
                'factorial': ('(d.factorial : ℝ)⁻¹ *', '(1 : ℝ) *'),
                'coefficient': ('2 * b / (d.factorial : ℝ) ^ 2 *', 'b / (d.factorial : ℝ) ^ 2 *'),
                'dimension': ('∀ (m : ℕ) (ν : ProbabilityMeasure (Space m)), Isotropic ν →',
                              '∀ (ν : ProbabilityMeasure (Space 1)), Isotropic ν →'),
            }
            for key, (old, new) in mutations.items():
                if old not in spec:
                    raise ValueError('Mutation anchor absent: ' + key)
                mutation = output / ('mutation-' + key)
                mutation.mkdir()
                # The dimension mutation also fixes the coefficient index to its chosen dimension.
                changed = spec.replace(old, new)
                if key == 'dimension':
                    segment_start = changed.index('def UniversalCumulant')
                    segment_end = changed.index('def Theorem31')
                    segment = changed[segment_start:segment_end].replace('Space m', 'Space 1').replace('Fin m', 'Fin 1').replace('logConcave m ν', 'logConcave 1 ν')
                    changed = changed[:segment_start] + segment + changed[segment_end:]
                (mutation / 'BKLIndependentSpecification.lean').write_text(changed)
                (mutation / 'BKLIndependentChecks.lean').write_bytes((HERE / 'Checks.lean.in').read_bytes())
                mutation_env = {**lean_env, 'LEAN_PATH': os.pathsep.join([str(mutation), *paths])}
                run('mutation-' + key + '-spec', [lean, '-DwarningAsError=true', '-R', str(mutation), '-o',
                    str(mutation / 'BKLIndependentSpecification.olean'), str(mutation / 'BKLIndependentSpecification.lean')], run_env=mutation_env)
                rejected = run('mutation-' + key + '-rejected', [lean, '-DwarningAsError=true', '-R', str(mutation),
                    str(mutation / 'BKLIndependentChecks.lean')], run_env=mutation_env, expected_failure=True)
                if not rejected_mutation(rejected, key):
                    raise ValueError('Mutation failed for an unexpected reason: ' + key)
            report['rejected_mutations'] = list(mutations)
        after = {str(p.relative_to(ROOT)): sha(p) for p in scope_files}
        if before != after:
            raise ValueError('Audit input sources changed during the run')
        if args.command == 'baseline':
            golden.write_text(pending_golden)
        report['source_unchanged'] = True
        report['status'] = 'passed'
    except (OSError, ValueError, RuntimeError, KeyError, subprocess.SubprocessError) as exc:
        report['errors'].append(str(exc))
    (output / 'report.json').write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
    latest = ROOT / 'build/reviews/2026-10-12-bkl-independent-targets/latest.json'
    latest.write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
    print('Pilot ' + report['status'] + ': ' + str((output / 'report.json').relative_to(ROOT)))
    for error in report['errors']:
        print(error, file=sys.stderr)
    return 0 if report['status'] == 'passed' else 1


if __name__ == '__main__':
    raise SystemExit(main())
