"""Exercise index isolation in a disposable Git repository, never the real worktree/index."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import update


class IndexIsolationTests(unittest.TestCase):
    def setUp(self):
        inputs = update.load_inputs()
        self.directory = tempfile.TemporaryDirectory(prefix='kls-index-test-')
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        for name, content in inputs.items():
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(content)
        # Do not inherit the task's private Git storage into the fixture repository.
        env = dict(os.environ)
        for name in ('GIT_INDEX_FILE', 'GIT_OBJECT_DIRECTORY', 'GIT_ALTERNATE_OBJECT_DIRECTORIES'):
            env.pop(name, None)
        self.env_patch = patch.dict(os.environ, env, clear=True)
        self.env_patch.start()
        self.addCleanup(self.env_patch.stop)
        self.root_patch = patch.object(update, 'ROOT', self.root)
        self.root_patch.start()
        self.addCleanup(self.root_patch.stop)
        self.git('init', '-q')
        self.git('add', '.')
        self.original = update.generate()

    def git(self, *args):
        return subprocess.run(['git', *args], cwd=self.root, check=True, capture_output=True)

    def test_unstaged_catalog_template_and_statement_edits_are_excluded(self):
        for name in ('research/progress/nodes.json', 'research/progress/portfolio.json',
                     'research/progress/literature.json', 'research/progress/README.md',
                     'formalization/blueprint/route-composition.yaml'):
            (self.root / name).write_text('unrelated unstaged invalid content\n')
        source = next(n for n in update.load_inputs() if n.endswith('.lean'))
        (self.root / source).write_text('unrelated unstaged invalid Lean\n')
        self.assertEqual(update.generate(), self.original)

    def test_staged_catalogs_template_and_statement_sources_change_the_digest(self):
        names = ('research/progress/nodes.json', 'research/progress/portfolio.json',
                 'research/progress/literature.json', 'research/progress/README.md',
                 'formalization/blueprint/route-composition.yaml')
        names += (next(n for n in update.load_inputs() if n.endswith('.lean')),)
        for name in names:
            with self.subTest(input=name):
                path = self.root / name
                original = path.read_text()
                if name.endswith(('.json', '.yaml')):
                    data = json.loads(original)
                    data['index_isolation_probe'] = True
                    path.write_text(json.dumps(data))
                else:
                    path.write_text(original + '\n<!-- template probe -->\n' if name.endswith('.md')
                                    else original + '\n-- statement source probe\n')
                self.assertEqual(update.generate(), self.original)
                self.git('add', name)
                self.assertNotEqual(update.generate()['STATUS.md'], self.original['STATUS.md'])
                path.write_text(original)
                self.git('add', name)
                self.assertEqual(update.generate(), self.original)

    def test_staged_route_policy_changes_display_without_changing_proof_markers(self):
        name = 'research/progress/nodes.json'
        path = self.root / name
        catalog = json.loads(path.read_text())
        # Move the CMH comparison into a shared group in this disposable fixture.
        shared = next(g for g in catalog['diagram']['groups'] if g['id'] == 'FOUND')
        cmh = next(g for g in catalog['diagram']['groups'] if g['id'] == 'CMH')
        cmh['nodes'].remove('MH')
        shared['nodes'].append('MH')
        path.write_text(json.dumps(catalog))
        self.assertEqual(update.generate(), self.original)
        self.git('add', name)
        changed = update.generate()
        self.assertIn('class MG,EG,FG,SG hypothesis;', changed['TREE.mmd'])
        self.assertIn('class MH todo;', changed['TREE.mmd'])
        self.assertNotEqual(changed['TREE.mmd'], self.original['TREE.mmd'])
        for name in changed:
            self.assertEqual(changed[name].count('✓'), self.original[name].count('✓'), name)

    def test_old_generated_template_bodies_are_not_canonical_inputs(self):
        path = self.root / 'research/progress/README.md'
        path.write_text(self.original['README.md'].replace('✓ Affine / isotropic', '○ Affine / isotropic', 1))
        self.git('add', 'research/progress/README.md')
        self.assertEqual(update.generate(), self.original)

    def test_missing_index_input_fails_instead_of_falling_back_to_worktree(self):
        self.git('rm', '--cached', 'research/progress/nodes.json')
        with self.assertRaises(subprocess.CalledProcessError):
            update.load_inputs()


if __name__ == '__main__':
    unittest.main()
