"""Only milestone tags trigger the local gate, and only for the clean checked-out commit."""
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from pre_push import milestone_commits

ZERO = '0' * 40


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

    def tag(self, name='milestone/test'):
        self.git('tag', '-am', 'Milestone', name)
        return f'refs/tags/{name} {self.git("rev-parse", name)} refs/tags/{name} {ZERO}\n'

    def test_branch_and_other_tag_pushes_are_ignored(self):
        self.source.write_text('theorem proved : True := by sorry\n')  # even when dirty
        branch = f'refs/heads/main {self.head} refs/heads/main {ZERO}\n'
        self.assertEqual(milestone_commits(self.root, branch), [])
        self.assertEqual(milestone_commits(self.root, self.tag('v1')), [])

    def test_annotated_milestone_at_clean_head_is_verified(self):
        (self.root / 'editor-notes.txt').write_text('Untracked local configuration\n')
        self.assertEqual(milestone_commits(self.root, self.tag()), [self.head])

    def test_dirty_tracked_file_rejects_milestone(self):
        update = self.tag()
        self.source.write_text('theorem proved : True := by sorry\n')
        with self.assertRaisesRegex(ValueError, 'Tracked files differ'):
            milestone_commits(self.root, update)

    def test_milestone_off_head_is_rejected(self):
        update = self.tag()
        self.source.write_text('theorem second : True := True.intro\n')
        self.git('commit', '-qam', 'Second snapshot')
        with self.assertRaisesRegex(ValueError, 'check out the tagged commit'):
            milestone_commits(self.root, update)

    def test_milestone_deletion_is_ignored(self):
        deletion = f'(delete) {ZERO} refs/tags/milestone/test {self.head}\n'
        self.assertEqual(milestone_commits(self.root, deletion), [])


if __name__ == '__main__':
    unittest.main()
