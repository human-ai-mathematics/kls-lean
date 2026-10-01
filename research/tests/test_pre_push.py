"""Protect the distinction between an outgoing commit and the verified checkout."""
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from pre_push import check_checkout


class PrePushTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.git('init', '-q')
        self.git('config', 'user.name', 'Gate test')
        self.git('config', 'user.email', 'gate@example.invalid')
        self.source = self.root / 'proof.lean'
        self.source.write_text('theorem proved : True := True.intro\n')
        self.git('add', 'proof.lean')
        self.git('commit', '-qm', 'Initial snapshot')
        self.head = self.git('rev-parse', 'HEAD')

    def git(self, *args):
        return subprocess.check_output(['git', *args], cwd=self.root, text=True).strip()

    def update(self, sha):
        return f'refs/heads/main {sha} refs/heads/main {"0" * 40}\n'

    def test_current_commit_accepts_unrelated_untracked_notes(self):
        (self.root / 'editor-notes.txt').write_text('Local configuration\n')
        self.assertTrue(check_checkout(self.root, self.update(self.head)))

    def test_dirty_proof_cannot_certify_committed_head(self):
        self.source.write_text('theorem proved : True := by sorry\n')
        with self.assertRaisesRegex(ValueError, 'Tracked files differ'):
            check_checkout(self.root, self.update(self.head))

    def test_other_outgoing_commit_requires_its_checkout(self):
        old = self.head
        self.source.write_text('theorem second : True := True.intro\n')
        self.git('add', 'proof.lean')
        self.git('commit', '-qm', 'Second snapshot')
        with self.assertRaisesRegex(ValueError, 'outgoing commit'):
            check_checkout(self.root, self.update(old))

    def test_annotated_milestone_at_head_and_ref_deletion(self):
        self.git('tag', '-am', 'Milestone', 'milestone/test')
        tag = self.git('rev-parse', 'milestone/test')
        self.assertTrue(check_checkout(self.root, self.update(tag)))
        self.assertFalse(check_checkout(self.root, self.update('0' * 40)))


if __name__ == '__main__':
    unittest.main()
