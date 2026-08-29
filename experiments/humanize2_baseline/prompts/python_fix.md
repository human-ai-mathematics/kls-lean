Fix the disposable Python baseline in this repository.

Read `AGENTS.md`, then inspect only the task files under
`experiments/humanize2_baseline/python_demo/`. The `add` function is intended to add its two
arguments, but the independent tests currently expose a bug.

Requirements:

1. Change only `experiments/humanize2_baseline/python_demo/calculator.py`.
2. Do not modify or weaken the tests.
3. Run exactly:
   `python3 -m unittest discover -s experiments/humanize2_baseline/python_demo -p 'test_*.py'`
4. Continue until that command exits successfully.
5. Inspect `git diff -- experiments/humanize2_baseline/python_demo` before finishing and
   confirm that the fix is minimal.

Do the work with shell/file tools; do not merely describe a patch. If the function is already
correct because this is a later Ralph round, rerun the tests and leave the files unchanged.
