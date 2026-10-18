"""Stdlib regressions use only disposable local Git repositories; no Lean or network."""
import ast
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest import mock

SOURCE = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('project_context_candidate', SOURCE / 'project_context.py')
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)
ProjectContext, ContextError = MOD.ProjectContext, MOD.ContextError

def digest(files):
    return hashlib.sha256(json.dumps(files, sort_keys=True, ensure_ascii=False, separators=(',', ':')).encode()).hexdigest()

def sha(data):
    return hashlib.sha256(data).hexdigest()

class ContextTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.root = Path(self.tmp.name)
        self.git('init', '-q'); self.git('config', 'user.email', 'test@example.invalid')
        self.git('config', 'user.name', 'Context Test')
        initial = {
            '.gitignore': 'build/\n.env*\n.cursor/\n', '.github/workflows/check.yml': 'name: check\n',
            '.githooks/pre-commit': '#!/bin/sh\n', 'README.md': 'original\n',
            'HANDOFF.md': '# Handoff\n## Current work and next step\nWork A.\n### Detail\nWork B.\n## Other\nExclude.\n',
            'research/tasks.json': {'nodes': {'node:old': {'note': 'old'}}},
            'research/a-series/ledger.yaml': {'nodes': [{'id': 'cert', 'status': 'recorded'}]},
            'research/progress/literature.json': {'papers': [{'id': 'P', 'remaining': 'Open main theorem'}], 'priorities': [{'papers': ['P']}]},
            'formalization/FunctionalInequalities.lean': 'import FunctionalInequalities.Demo\n',
            'formalization/FunctionalInequalities/Demo.lean': 'theorem demo : True := by trivial\n',
            'formalization/lean-toolchain': 'leanprover/lean4:v4.33.0\n',
            'formalization/lakefile.toml': 'name = "fixture"\n', 'formalization/lake-manifest.json': {},
            'research/APIIndex.lean': '-- driver\n', 'research/api_index.py': '# driver\n',
            'research/module_inventory.py': '# inventory\n', 'research/verify.py': '# verify\n',
            'research/atlas.py': '# atlas\n', 'research/audits/KLS/Classical/Client.lean.in': '-- client\n',
            'research/audits/KLS/Classical/check.py': '# check\n',
        }
        for p, value in initial.items(): self.write(p, value)
        self.commit(); self.ctx = ProjectContext(self.root)
    def tearDown(self): self.tmp.cleanup()
    def git(self, *args, root=None, data=None):
        env = {k: v for k, v in os.environ.items() if not k.startswith('GIT_')}
        env['GIT_OPTIONAL_LOCKS'] = '0'
        return subprocess.check_output(['git', '-C', str(root or self.root), *args], input=data, env=env, stderr=subprocess.DEVNULL).decode().strip()
    def write(self, path, value):
        p = self.root / path; p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps(value) if isinstance(value, (dict, list)) else value)
    def commit(self):
        self.git('add', '.'); self.git('commit', '-qm', 'fixture')
        return self.git('rev-parse', 'HEAD')
    def snapshot(self, view='head', revision=None): return self.ctx.project_snapshot(view, revision)['snapshot']
    def report(self, sid, scope='full', **extra):
        files = self.ctx._scope_files(self.ctx._record(sid)['files'], scope)[0]
        return {'version': 1, 'scope': scope, 'started_utc': '20261019T000000Z',
                'snapshot': {'files': files, 'sha256': digest(files)}, 'status': 'passed',
                'gates': [{'name': 'fixture', 'exit_code': 0}], 'errors': [], 'trust_scope': 'local claim', **extra}
    def receipt(self, data, name='20261019T000000Z'):
        self.write('build/verification/' + name + '/report.json', data)
    def api(self, sid, **updates):
        rec = self.ctx._record(sid); inputs = {p: rec['files'][p] for p in self.ctx._api_expected(rec['files'])}
        row = {'name': 'demo', 'type': 'True', 'module': 'FunctionalInequalities.Demo', 'source_path': 'formalization/FunctionalInequalities/Demo.lean', 'source_line': 1, 'source_end_line': 1, 'docstring': None}
        self.write('build/api-index/public-api.json', [row]); raw = (self.root / 'build/api-index/public-api.json').read_bytes()
        manifest = {'format': 1, 'inputs': inputs, 'input_digest': sha(json.dumps(inputs, sort_keys=True, separators=(',', ':')).encode()),
            'outputs': {k: sha(raw) if k == 'public-api.json' else '0'*64 for k in ('compiler.json', 'public-api.json', 'index.html', 'Observe.lean')},
            'source_head': rec['head'], 'source_binding': 'worktree content hashes', 'toolchain': 'leanprover/lean4:v4.33.0',
            'source_modules': 1, 'imported_modules': ['FunctionalInequalities', 'FunctionalInequalities.Demo'],
            'public_declarations': 1, 'with_source_ranges': 1, 'with_docstrings': 0, 'trust_scope': 'compiler observation', **updates}
        self.write('build/api-index/manifest.json', manifest); return manifest

    def test_real_digest_precommit_head_mismatch_and_no_receipts(self):
        sid = self.snapshot(); self.assertFalse(self.ctx.verification_status(sid)['accepted'])
        report = self.report(sid, head='0'*40); self.receipt(report)
        self.assertTrue(self.ctx.verification_status(sid)['accepted'])
        report['snapshot']['sha256'] = '0'*64; self.receipt(report)
        self.assertFalse(self.ctx.verification_status(sid)['accepted'])
    def test_all_safe_public_files_hash_but_text_boundary_is_narrow(self):
        sid = self.snapshot(); rec = self.ctx._record(sid)
        for p in ('.gitignore', '.github/workflows/check.yml', '.githooks/pre-commit', 'research/verify.py'):
            self.assertIn(p, rec['files']); self.assertFalse(self.ctx.allowed(p))
            with self.assertRaises(ContextError): self.ctx._read_record(rec, p)
        self.assertTrue(self.ctx.project_snapshot()['content_binding']['complete'])
        for p in ('examples/privateREADME.md', '.cursor/private.lean', 'research/decisions/old.md', 'formalization/FunctionalInequalities/.env.lean'):
            self.assertFalse(self.ctx.allowed(p))
    def test_extra_missing_changed_and_unfiltered_receipt_digest(self):
        sid = self.snapshot(); report = self.report(sid); files = report['snapshot']['files'].copy()
        removed = 'research/APIIndex.lean'; del files[removed]
        files['research/audits/extra.lean'] = '0'*64; files['README.md'] = '1'*64
        report['snapshot'] = {'files': files, 'sha256': digest(files)}; self.receipt(report)
        result = self.ctx.verification_status(sid); a = result['latest']['assessment']
        self.assertFalse(result['accepted']); self.assertTrue(a['digest_valid'])
        self.assertEqual((a['missing_count'], a['extra_count'], a['different_count']), (1, 1, 1))
    def test_lean_scope_binds_audits_templates_pins_and_tools(self):
        sid = self.snapshot(); self.receipt(self.report(sid, 'lean-only'))
        self.assertTrue(self.ctx.verification_status(sid, 'lean-only')['accepted'])
        self.assertFalse(self.ctx.verification_status(sid, 'full')['accepted'])
        self.assertEqual(self.ctx.verification_status(sid, 'downstream')['availability'], 'unavailable')
        for p in ('research/audits/KLS/Classical/Client.lean.in', 'research/audits/KLS/Classical/check.py', 'formalization/lean-toolchain', 'research/verify.py'):
            with self.subTest(path=p):
                report = self.report(sid, 'lean-only'); report['snapshot']['files'][p] = '0'*64
                report['snapshot']['sha256'] = digest(report['snapshot']['files']); self.receipt(report)
                self.assertFalse(self.ctx.verification_status(sid, 'lean-only')['accepted'])
    def test_latest_malformed_incomplete_unknown_null_and_failed(self):
        sid = self.snapshot(); self.receipt(self.report(sid), '20261018T000000Z')
        variants = ['{bad', [], {**self.report(sid), 'scope': 'unknown'}, self.report(sid, gates=[]),
                    self.report(sid, gates=[{'name': 'unfinished', 'exit_code': None}]),
                    self.report(sid, gates=[{'name': 'bool', 'exit_code': False}]),
                    self.report(sid, errors=['failed'], status='failed'),
                    self.report(sid, gates=[{'name': 'failed', 'exit_code': 1}])]
        for report in variants:
            with self.subTest(report=report):
                self.receipt(report); result = self.ctx.verification_status(sid)
                self.assertFalse(result['accepted']); self.assertIn('20261019', result['latest_observed']['path'])
        self.receipt(self.report(sid, 'lean-only'))
        result = self.ctx.verification_status(sid)
        self.assertTrue(result['accepted']); self.assertEqual(result['latest_observed']['scope'], 'lean-only')
        self.assertIn('20261018', result['latest_scope_compatible']['path'])
    def test_malformed_attempt_cannot_be_hidden_by_a_later_other_scope(self):
        sid = self.snapshot()
        self.receipt(self.report(sid), '20261018T000000Z')
        self.receipt('{bad', '20261019T000000Z')
        self.receipt(self.report(sid, 'lean-only'), '20261020T000000Z')
        result = self.ctx.verification_status(sid, 'full')
        self.assertFalse(result['accepted'])
        self.assertEqual(result['unresolved_newer_attempt_count'], 1)
        self.assertTrue(self.ctx.verification_status(sid, 'lean-only')['accepted'])
        self.receipt(self.report(sid), '20261021T000000Z')
        self.assertTrue(self.ctx.verification_status(sid, 'full')['accepted'])

    def test_more_than_fifty_receipts_never_exact_accepts(self):
        sid = self.snapshot()
        for i in range(55): self.receipt(self.report(sid), f'20261019T{i:06d}Z')
        result = self.ctx.verification_status(sid)
        self.assertFalse(result['accepted']); self.assertFalse(result['scan_complete'])
        self.assertEqual(result['paging']['total'], 50)
        self.assertIn('000054', result['latest_observed']['path'])
    def test_immutable_head_revision_survive_divergent_branch_and_index(self):
        old = self.git('rev-parse', 'HEAD'); sid = self.snapshot(); revision = self.snapshot(revision=old)
        self.git('checkout', '-qb', 'other'); self.write('research/tasks.json', {'nodes': {'new': {}}}); new = self.commit()
        for handle in (sid, revision):
            result = self.ctx.project_status(handle)
            self.assertEqual(result['task_nodes'][0]['id'], 'node:old')
            self.assertEqual(result['metadata']['snapshot_head'], old); self.assertEqual(result['metadata']['head'], new)
        self.assertIn('Work A.', self.ctx.handoff_resource(old))
    def test_index_worktree_selection_stale_and_real_index_unchanged(self):
        self.write('research/tasks.json', {'nodes': {'staged': {}}}); self.git('add', 'research/tasks.json')
        self.write('research/tasks.json', {'nodes': {'unstaged': {}}})
        before = self.ctx._index_sha(); head = self.snapshot(); index = self.snapshot('index'); work = self.snapshot('worktree')
        for sid, expected in ((head, 'node:old'), (index, 'staged'), (work, 'unstaged')):
            self.assertEqual(self.ctx.project_status(sid)['task_nodes'][0]['id'], expected)
            self.ctx.work_next(sid); self.ctx.claim_explain(sid, expected); self.ctx.verification_status(sid)
            self.ctx.changes_review(self.git('rev-parse', 'HEAD'), sid)
        self.assertEqual(before, self.ctx._index_sha())
        self.write('README.md', 'mutation\n')
        with self.assertRaises(ContextError): self.ctx.project_status(work)
        self.git('add', 'README.md')
        with self.assertRaises(ContextError): self.ctx.project_status(index)
    def test_restored_content_metadata_does_not_refresh_real_index(self):
        original = (self.root/'README.md').read_bytes()
        self.write('README.md', 'temporary mutation\n'); (self.root/'README.md').write_bytes(original)
        before = self.ctx._index_sha(); sid = self.snapshot('worktree')
        self.ctx.project_status(sid); self.ctx.work_next(sid)
        self.assertEqual(before, self.ctx._index_sha())
    def test_untracked_addition_and_missing_tracked_files_bind(self):
        self.write('research/new_tool.py', '# new\n'); (self.root/'README.md').unlink()
        sid = self.snapshot('worktree'); files = self.ctx._record(sid)['files']
        self.assertIn('research/new_tool.py', files); self.assertIsNone(files['README.md'])
        self.receipt(self.report(sid)); self.assertTrue(self.ctx.verification_status(sid)['accepted'])
        self.write('research/audits/added.lean', '-- new\n')
        with self.assertRaises(ContextError): self.ctx.verification_status(sid)
    def test_capture_races_and_postvalidation_read_race(self):
        source = self.ctx._source_map
        def changed(*args):
            result = source(*args); self.write('README.md', 'stage\n'); self.git('add', 'README.md'); return result
        with mock.patch.object(self.ctx, '_source_map', side_effect=changed):
            with self.assertRaises(ContextError): self.snapshot('index')
        sid = self.snapshot('worktree'); validate = self.ctx._validate
        def aftercheck(handle):
            rec = validate(handle); self.write('research/tasks.json', {'nodes': {'raced': {}}}); return rec
        with mock.patch.object(self.ctx, '_validate', side_effect=aftercheck):
            with self.assertRaises(ContextError): self.ctx.project_status(sid)
        paths = self.ctx._work_paths; calls = [0]
        def racepaths():
            calls[0] += 1
            if calls[0] == 2: self.write('README.md', 'midcapture\n')
            return paths()
        with mock.patch.object(self.ctx, '_work_paths', side_effect=racepaths):
            with self.assertRaises(ContextError): self.snapshot('worktree')
    def test_secret_tracked_file_is_never_read_and_prevents_green(self):
        self.write('.env', 'sensitive token\n'); self.git('add', '-f', '.env'); self.git('commit', '-qm', 'secret fixture')
        original = self.ctx._blobs
        def safe_only(oids):
            self.assertNotIn('.env', oids); return original(oids)
        with mock.patch.object(self.ctx, '_blobs', side_effect=safe_only): sid = self.snapshot()
        self.assertFalse(self.ctx.project_snapshot()['content_binding']['complete'])
        self.receipt(self.report(sid)); self.assertFalse(self.ctx.verification_status(sid)['accepted'])
        self.assertNotIn('sensitive token', json.dumps(self.ctx.project_status(sid)))
    def test_artifact_and_source_symlinks_final_parent_inside_and_escape(self):
        self.write('.cursor/private.json', '{}'); target = self.root/'.cursor/private.json'
        for escape in (target, self.root/'README.md', Path('/etc/passwd')):
            p = self.root/'build/api-index/public-api.json'; p.parent.mkdir(parents=True, exist_ok=True); p.symlink_to(escape)
            with self.assertRaises(ContextError): self.ctx._fixed_file(p)
            p.unlink()
        parent = self.root/'build/api-index'; parent.rmdir(); parent.symlink_to(self.root/'.cursor')
        with self.assertRaises(ContextError): self.ctx._fixed_file(parent/'private.json')
        with self.assertRaises(ContextError): self.ctx._fixed_file(parent/'manifest.json')
        source = self.root/'formalization/FunctionalInequalities/link.lean'; source.symlink_to(self.root/'README.md')
        with self.assertRaises(ContextError): self.snapshot('worktree')
        self.git('add', str(source.relative_to(self.root)))
        with self.assertRaises(ContextError): self.snapshot('index')
    def test_parameters_registry_types_deep_json_and_bounds(self):
        for args in (({},), ('head', {}), ('worktree', '0'*40), ('head', '--all')):
            with self.assertRaises(ContextError): self.ctx.project_snapshot(*args)
        sid = self.snapshot()
        for scope in ({}, [], 'bogus'):
            with self.assertRaises(ContextError): self.ctx.verification_status(sid, scope)
        for offset, limit in ((True, 2), (-1, 1), (0, 51), (0, {})):
            with self.assertRaises(ContextError): self.ctx.project_status(sid, offset, limit)
        with self.assertRaises(ContextError): MOD._bounded_json(('['*40+'0'+']'*40).encode())
        with mock.patch.object(MOD, 'MAX_FILE', 8):
            with self.assertRaises(ContextError): self.ctx._blobs({'x': self.git('rev-parse', 'HEAD:README.md')})
        self.write('research/tasks.json', {'nodes': []}); self.commit(); sid = self.snapshot()
        for fn in (self.ctx.project_status, lambda x: self.ctx.claim_explain(x, 'anything')):
            with self.assertRaises(ContextError): fn(sid)
    def test_record_paging_provenance_heading_and_truncation(self):
        self.write('research/extra_tool.py', '# safe hash-only input\n')
        self.write('research/tasks.json', {'nodes': {f'n{i}': {'note': 'a'*9000} for i in range(80)}})
        self.write('research/progress/literature.json', {'papers': [{'id': f'P{i}', 'remaining': 'open'} for i in range(80)], 'priorities': [{'papers': ['P79']}]})
        sid = self.snapshot('worktree'); result = self.ctx.project_status(sid, 79, 1)
        self.assertEqual(len(result['metadata']['source_refs']), 20)
        self.assertTrue(result['metadata']['source_refs_truncated'])
        self.assertGreater(result['metadata']['source_ref_count'], 20)
        self.assertEqual(result['papers'][0]['record']['id'], 'P79'); self.assertEqual(result['paper_paging']['total'], 80)
        self.assertEqual(result['papers'][0]['source']['json_pointer'], '/papers/79')
        self.assertIn('<truncated>', result['task_nodes'][0]['record']['note'])
        match = self.ctx.claim_explain(sid, 'P79')['literature_matches'][0]
        self.assertEqual(match['source']['json_pointer'], '/papers/79/id')
        work = self.ctx.work_next(sid)['handoff_work']; self.assertIn('Work B.', work); self.assertNotIn('Exclude.', work)
        self.assertLess(len(json.dumps(self.ctx.project_status(sid, 0, 50))), 1000000)
    def test_api_exact_producers_and_stale_missing_extra_driver_or_library(self):
        sid = self.snapshot(); self.api(sid)
        self.assertEqual(self.ctx.claim_explain(sid, 'demo')['compiler']['type'], 'True')
        for p in ('research/audits/extra.lean', 'solutions/Extra.lean'):
            self.write(p, '-- audit\n')
        extra = self.snapshot('worktree')
        self.assertIsNotNone(self.ctx.claim_explain(extra, 'demo')['compiler'])
        for p in ('research/APIIndex.lean', 'formalization/FunctionalInequalities/New.lean', 'formalization/lean-toolchain'):
            with self.subTest(path=p):
                original = (self.root/p).read_bytes() if (self.root/p).exists() else None
                self.write(p, '-- mutation\n'); current = self.snapshot('worktree')
                self.assertIsNone(self.ctx.claim_explain(current, 'demo')['compiler'])
                if original is None: (self.root/p).unlink()
                else: (self.root/p).write_bytes(original)
        sid = self.snapshot(); manifest = self.api(sid); manifest['inputs'] = {}; self.write('build/api-index/manifest.json', manifest)
        self.assertIsNone(self.ctx.claim_explain(sid, 'demo')['compiler'])
    def test_api_metadata_digest_output_and_artifact_race(self):
        sid = self.snapshot()
        for change in ({'input_digest': '0'*64}, {'source_modules': []}, {'with_docstrings': False}, {'trust_scope': {}}, {'imported_modules': []}):
            self.api(sid, **change); self.assertIsNone(self.ctx.claim_explain(sid, 'demo')['compiler'])
        self.api(sid); self.write('build/api-index/public-api.json', [])
        self.assertIsNone(self.ctx.claim_explain(sid, 'demo')['compiler'])
        self.api(sid); original = self.ctx._fixed_file; count = [0]
        def race(path):
            count[0] += 1
            if count[0] == 3: self.write('build/api-index/manifest.json', {})
            return original(path)
        with mock.patch.object(self.ctx, '_fixed_file', side_effect=race):
            self.assertIsNone(self.ctx.claim_explain(sid, 'demo')['compiler'])
    def test_git_environment_injection_and_wrapper_surface(self):
        with mock.patch.dict(os.environ, {'GIT_CONFIG_COUNT': '1', 'GIT_CONFIG_KEY_0': 'core.hooksPath', 'GIT_CONFIG_VALUE_0': '/bad', 'GIT_DIR': '/bad'}):
            self.assertEqual(ProjectContext(self.root)._head(), self.git('rev-parse', 'HEAD'))
        tree = ast.parse((SOURCE/'context_mcp.py').read_text()); tools = []
        for node in ast.walk(tree):
            if isinstance(node, ast.FunctionDef):
                for d in node.decorator_list:
                    if isinstance(d, ast.Call) and isinstance(d.func, ast.Attribute) and d.func.attr == 'tool':
                        tools.append(next(k.value.value for k in d.keywords if k.arg == 'name'))
        self.assertEqual(sorted(tools), sorted(['project_snapshot','project_status','verification_status','claim_explain','changes_review','work_next']))
        self.assertIn('transport="stdio"', (SOURCE/'context_mcp.py').read_text())
    def test_optional_sdk_stdio_round_trip(self):
        try:
            import mcp
        except ImportError:
            self.skipTest('optional pinned SDK is not installed in this interpreter')
        import asyncio
        import sys
        async def run():
            params = mcp.StdioServerParameters(command=sys.executable,
                args=['-B', '-m', 'research.context_mcp', '--repo', str(self.root)],
                cwd=SOURCE.parent, env={'PYTHONDONTWRITEBYTECODE': '1', 'GIT_OPTIONAL_LOCKS': '0'})
            before = self.ctx._index_sha()
            async with mcp.Client(params) as client:
                listed = await client.list_tools()
                self.assertEqual(len(listed.tools), 6)
                self.assertEqual({t.name for t in listed.tools}, {'project_snapshot','project_status','verification_status','claim_explain','changes_review','work_next'})
                for tool in listed.tools:
                    self.assertTrue(tool.annotations.read_only_hint)
                    self.assertFalse(tool.annotations.destructive_hint)
                templates = await client.list_resource_templates()
                self.assertEqual(str(templates.resource_templates[0].uri_template), 'project://kls/{commit}/handoff')
                result = await client.call_tool('project_snapshot', {'view': 'head'})
                value = result.structured_content or json.loads(result.content[0].text)
                sid = value['snapshot']
                work = await client.call_tool('work_next', {'snapshot': sid})
                work_value = work.structured_content or json.loads(work.content[0].text)
                self.assertIn('Work B.', work_value['handoff_work'])
                resource = await client.read_resource('project://kls/'+self.git('rev-parse', 'HEAD')+'/handoff')
                self.assertIn('Work A.', resource.contents[0].text)
            self.assertEqual(before, self.ctx._index_sha())
        asyncio.run(run())

if __name__ == '__main__': unittest.main(verbosity=2)
