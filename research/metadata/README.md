# Offline metadata schema

`formalization-v0.4.schema.json` and `LICENSE` are unmodified copies from
[formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml/tree/99c678e569c7c4c0772db297c5ddd5e4c9b6322e),
at the revision already declared by all three metadata documents. `UPSTREAM.json` records
the exact source URLs, revision and SHA-256 hashes. The local gate verifies those hashes and
uses the bundled schema without network access. Review the pin and metadata together before
updating it; the verifier never refreshes a schema or rewrites metadata.

Install the direct validation dependencies from
[`requirements-validation.txt`](../requirements-validation.txt), then run
`python3 research/check_metadata.py` from the repository root. The gate validates the root,
OpenAI bridge and Palomar metadata against the pinned v0.4 schema. It also rejects duplicate
or non-string mapping keys, non-JSON scalars, unsupported profile versions and malformed MSC
codes. Every MSC code must be quoted, in either a flow or block list: YAML 1.1 accepts bare
`60E15` as a string, while the browser's YAML 1.2 parser treats it as a number.

This is a local schema and encoding check. The permissive upstream schema allows project
extensions; this gate does not establish their mathematical claims, validate every Palomar
intake rule, or replace the official browser/server preflight and actual registration.
