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
        # Do not inherit the task's temporary index into the fixture repository.
        env = dict(os.environ)
        env.pop('GIT_INDEX_FILE', None)
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
                     'research/progress/literature.json', 'research/progress/README.md'):
            (self.root / name).write_text('unrelated unstaged invalid content\n')
        source = next(n for n in update.load_inputs() if n.endswith('.lean'))
        (self.root / source).write_text('unrelated unstaged invalid Lean\n')
        self.assertEqual(update.generate(), self.original)

    def test_staged_catalogs_template_and_statement_sources_change_the_digest(self):
        names = ('research/progress/nodes.json', 'research/progress/portfolio.json',
                 'research/progress/literature.json', 'research/progress/README.md')
        names += (next(n for n in update.load_inputs() if n.endswith('.lean')),)
        for name in names:
            with self.subTest(input=name):
                path = self.root / name
                original = path.read_text()
                if name.endswith('.json'):
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
