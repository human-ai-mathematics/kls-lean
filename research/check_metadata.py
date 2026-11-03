#!/usr/bin/env python3
"""Check the three metadata documents offline, including portable MSC string encoding.

This validates metadata structure and encoding, not mathematical claims or Palomar acceptance.
Install the local validation dependencies from research/requirements-validation.txt.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

try:
    import yaml
    from jsonschema import Draft7Validator
except ImportError as error:
    raise ImportError(f"{error.name} is missing; install the local validation dependencies with "
                      "`python3 -m pip install -r research/requirements-validation.txt`") from error

ROOT = Path(__file__).resolve().parents[1]
METADATA_FILES = ("formalization.yaml", "integrations/openai/formalization.yaml",
                  "integrations/palomar/formalization.yaml")
SCHEMA_DIR = Path("research/metadata")
SCHEMA_FILE = "formalization-v0.4.schema.json"
SCHEMA_REVISION = "99c678e569c7c4c0772db297c5ddd5e4c9b6322e"


class MetadataLoader(yaml.SafeLoader):
    """Reject duplicate/non-string mapping keys instead of silently replacing fields."""

    def construct_mapping(self, node, deep=False):
        seen = set()
        for key, _ in node.value:
            if key.tag != "tag:yaml.org,2002:str":
                raise yaml.constructor.ConstructorError(
                    None, None, "metadata mapping keys must be strings; YAML merges are not allowed",
                    key.start_mark)
            if key.value in seen:
                raise yaml.constructor.ConstructorError(
                    None, None, f"duplicate metadata key: {key.value}", key.start_mark)
            seen.add(key.value)
        return super().construct_mapping(node, deep=deep)


def schema_validator(root: Path) -> Draft7Validator:
    directory = root / SCHEMA_DIR
    lock = json.loads((directory / "UPSTREAM.json").read_text(encoding="utf-8"))
    if lock["revision"] != SCHEMA_REVISION or set(lock["files"]) != {SCHEMA_FILE, "LICENSE"}:
        raise ValueError("metadata schema inventory/revision differs from the reviewed pin")
    for name, record in lock["files"].items():
        content = (directory / name).read_bytes()
        if hashlib.sha256(content).hexdigest() != record["sha256"]:
            raise ValueError(f"metadata schema provenance hash differs: {name}")
    schema = json.loads((directory / SCHEMA_FILE).read_text(encoding="utf-8"))
    Draft7Validator.check_schema(schema)
    return Draft7Validator(schema)


def mapping_field(node, name):
    if isinstance(node, yaml.MappingNode):
        return next((value for key, value in node.value if key.value == name), None)
    return None


def check_document(text: str, validator: Draft7Validator) -> list[str]:
    """Use one captured document for both schema validation and scalar-style checks."""
    loader = MetadataLoader(text)
    try:
        node = loader.get_single_node()
        data = loader.construct_document(node) if node is not None else None
        # Metadata is exchanged as JSON by the browser: dates, cycles and NaN are not portable.
        json.dumps(data, allow_nan=False)
    except (yaml.YAMLError, TypeError, ValueError) as error:
        return [f"invalid metadata YAML: {error}"]
    finally:
        loader.dispose()
    errors = []
    for error in sorted(validator.iter_errors(data), key=lambda item: str(list(item.path))):
        path = ".".join(map(str, error.path)) or "document"
        errors.append(f"{path}: {error.message}")
    if not isinstance(data, dict) or data.get("version") != "v0.4":
        errors.append("version: expected the reviewed v0.4 profile")
    codes = mapping_field(mapping_field(node, "classification"), "msc2020")
    if isinstance(codes, yaml.SequenceNode):
        for index, code in enumerate(codes.value):
            field = f"classification.msc2020.{index}"
            if not isinstance(code, yaml.ScalarNode) or code.style not in {"'", '"'}:
                errors.append(f"{field}: quote MSC codes to preserve strings in YAML 1.1 and 1.2")
            valid_code = isinstance(code, yaml.ScalarNode) and re.fullmatch(
                r"[0-9]{2}[A-Z-][0-9]{2}", code.value)
            if not valid_code:
                errors.append(f"{field}: expected a five-character MSC2020 code, such as 60E15")
    return errors


def check_metadata(root: Path) -> list[str]:
    try:
        validator = schema_validator(root)
    except (OSError, ValueError, KeyError) as error:
        return [f"metadata schema: {error}"]
    errors = []
    for name in METADATA_FILES:
        try:
            errors.extend(f"{name}: {error}" for error in check_document(
                (root / name).read_text(encoding="utf-8"), validator))
        except (OSError, UnicodeError) as error:
            errors.append(f"{name}: {error}")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    args = parser.parse_args()
    errors = check_metadata(args.root.resolve())
    for error in errors:
        print(error, file=sys.stderr)
    print(f"Metadata: {len(METADATA_FILES)} documents; {len(errors)} error(s).")
    return int(bool(errors))


if __name__ == "__main__":
    raise SystemExit(main())
