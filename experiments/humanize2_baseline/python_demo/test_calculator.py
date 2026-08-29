"""Independent checks for the disposable Humanize2 Python fixture."""

import unittest

from calculator import add


class AddTests(unittest.TestCase):
    def test_positive_integers(self) -> None:
        self.assertEqual(add(2, 3), 5)

    def test_negative_integer(self) -> None:
        self.assertEqual(add(-4, 7), 3)


if __name__ == "__main__":
    unittest.main()
