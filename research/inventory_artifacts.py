#!/usr/bin/env python3
'''Read-only inventory and historical-index candidate generator.

The default output is the ignored build/file-management directory. This tool never
moves, deletes, links, clones, archives, or rewrites repository artifacts. It reads
artifact contents only for the narrowly scoped nonignored reference scan and never
reads credential or configuration sources.
'''

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from urllib.parse import quote

SKIP_DIRS = {'.git', '.lake', 'node_modules'}
CREDENTIAL_PARTS = {'.aws', '.config', '.gnupg', '.ssh', 'credentials', 'secrets'}
CONFIG_SUFFIXES = {'.cfg', '.conf', '.env', '.ini', '.json', '.lock', '.toml', '.xml', '.yaml', '.yml'}
TEXT_SUFFIXES = {'.bash', '.csv', '.diff', '.log', '.lean', '.md', '.mmd', '.patch', '.py', '.rst', '.sh', '.tex', '.tsv', '.txt', '.jsonl'}
REFERENCE_RE = re.compile(r'build/(?:reviews|verification)/[A-Za-z0-9._+~=:@/-]+')
DATE_RE = re.compile(r'^[0-9]{4}-[0-9]{2}-[0-9]{2}')
RETENTION_ROLES = frozenset({'current', 'adopted', 'historical_candidate', 'rebuildable'})


def fail(message: str) -> None:
    raise RuntimeError(message)


def relative(root: Path, path: Path) -> str:
    return path.relative_to(root).as_posix()


def lexical_path(root: Path, value: str) -> Path:
    raw = Path(value)
    candidate = raw if raw.is_absolute() else root / raw
    return Path(os.path.abspath(os.fspath(candidate)))


def reject_symlink_components(path: Path, anchor: Path) -> None:
    try:
        remainder = path.relative_to(anchor)
    except ValueError:
        fail(f'path is outside lexical anchor: {path}')
    cursor = anchor
    if cursor.is_symlink():
        fail(f'path component is a symlink: {cursor}')
    for part in remainder.parts:
        cursor /= part
        if cursor.is_symlink():
            fail(f'path component is a symlink: {cursor}')


def walk_files(base: Path, exclusions: dict[str, int]):
    if not base.is_dir() or base.is_symlink():
        fail(f'not a real directory: {base}')
    for current, directories, files in os.walk(base, topdown=True, followlinks=False):
        current_path = Path(current)
        kept_directories = []
        for name in sorted(directories):
            path = current_path / name
            if path.is_symlink():
                exclusions['symlink_directories'] += 1
            elif name == '.lake':
                exclusions['nested_lake_directories'] += 1
            elif name == '.git':
                exclusions['git_directories'] += 1
            elif name == 'node_modules':
                exclusions['node_modules_directories'] += 1
            else:
                kept_directories.append(name)
        directories[:] = kept_directories
        for name in sorted(files):
            path = current_path / name
            if path.is_symlink():
                exclusions['symlink_files'] += 1
                continue
            try:
                is_file = path.is_file()
            except OSError:
                exclusions['failed_file_checks'] += 1
                continue
            if not is_file:
                exclusions['nonregular_files'] += 1
                continue
            yield path


def inventory_tree(root: Path, run: Path) -> dict:
    total = 0
    count = 0
    extension_bytes: dict[str, int] = {}
    exclusions = {
        'nested_lake_directories': 0,
        'git_directories': 0,
        'node_modules_directories': 0,
        'symlink_directories': 0,
        'symlink_files': 0,
        'nonregular_files': 0,
        'failed_file_checks': 0,
        'failed_stats': 0,
    }
    artifacts = []
    for path in walk_files(run, exclusions):
        try:
            size = path.stat(follow_symlinks=False).st_size
        except OSError:
            exclusions['failed_stats'] += 1
            continue
        artifact_path = relative(root, path)
        total += size
        count += 1
        suffix = path.suffix.lower() or '[none]'
        extension_bytes[suffix] = extension_bytes.get(suffix, 0) + size
        artifacts.append({'path': artifact_path, 'logical_bytes': size})
    return {
        'path': relative(root, run),
        'files': count,
        'logical_bytes': total,
        'extension_logical_bytes': dict(sorted(extension_bytes.items())),
        'artifacts': artifacts,
        'traversal_exclusions': exclusions,
    }


def list_runs(root: Path, area_name: str) -> list[dict]:
    area = root / area_name
    if area.is_symlink() or not area.is_dir():
        fail(f'missing or invalid inventory area: {area}')
    runs = []
    loose = {'path': area_name, 'area_root_files_only': True, 'files': 0,
             'logical_bytes': 0, 'extension_logical_bytes': {}, 'artifacts': [],
             'traversal_exclusions': {'symlink_entries': 0, 'excluded_directory_entries': 0,
                                      'nonregular_entries': 0, 'failed_stats': 0}}
    for child in sorted(area.iterdir(), key=lambda item: item.name):
        if child.is_symlink():
            loose['traversal_exclusions']['symlink_entries'] += 1
        elif child.is_dir():
            if child.name in SKIP_DIRS:
                loose['traversal_exclusions']['excluded_directory_entries'] += 1
            else:
                runs.append(inventory_tree(root, child))
        elif child.is_file():
            try:
                size = child.stat(follow_symlinks=False).st_size
            except OSError:
                loose['traversal_exclusions']['failed_stats'] += 1
                continue
            loose['files'] += 1
            loose['logical_bytes'] += size
            suffix = child.suffix.lower() or '[none]'
            loose['extension_logical_bytes'][suffix] = loose['extension_logical_bytes'].get(suffix, 0) + size
            loose['artifacts'].append({'path': relative(root, child), 'logical_bytes': size})
        else:
            loose['traversal_exclusions']['nonregular_entries'] += 1
    loose['extension_logical_bytes'] = dict(sorted(loose['extension_logical_bytes'].items()))
    return [loose, *runs]


def git_paths(root: Path) -> list[str]:
    try:
        result = subprocess.run(
            ['git', 'ls-files', '-co', '--exclude-standard', '-z'],
            cwd=root,
            check=True,
            capture_output=True,
            shell=False,
        )
    except FileNotFoundError as exc:
        fail(f'git is required for the nonignored reference scan: {exc}')
    except subprocess.CalledProcessError as exc:
        fail(f'git ls-files failed with status {exc.returncode}')
    return sorted({os.fsdecode(item) for item in result.stdout.split(b"\0") if item})


def readable_source(path: Path) -> tuple[bool, str]:
    parts = set(path.parts)
    if parts & CREDENTIAL_PARTS:
        return False, 'credential_path'
    if path.suffix.lower() in CONFIG_SUFFIXES:
        return False, 'configuration_suffix'
    if path.suffix.lower() not in TEXT_SUFFIXES:
        return False, 'non_text_suffix'
    return True, ''


def source_class(path: str) -> str:
    if path == 'HANDOFF.md':
        return 'current_handoff'
    if path.startswith('research/decisions/') or path.startswith('research/handoffs/'):
        return 'dated_records'
    return 'other_nonignored_text'


def clean_target(value: str) -> str:
    return value.rstrip('.,;:!?)]}')


def reference_scan(root: Path) -> tuple[dict[str, list[dict]], dict[str, int]]:
    found: dict[str, set[tuple[str, str]]] = {
        'current_handoff': set(),
        'dated_records': set(),
        'other_nonignored_text': set(),
    }
    stats = {
        'git_paths_considered': 0,
        'scanned_utf8_text_files': 0,
        'skipped_symlinks': 0,
        'skipped_nonfiles': 0,
        'skipped_credential_paths': 0,
        'skipped_configuration_files': 0,
        'skipped_non_text_files': 0,
        'skipped_nul_binary_files': 0,
        'failed_reads': 0,
        'non_utf8_reads': 0,
    }
    for name in git_paths(root):
        stats['git_paths_considered'] += 1
        path = root / name
        if path.is_symlink():
            stats['skipped_symlinks'] += 1
            continue
        if not path.is_file():
            stats['skipped_nonfiles'] += 1
            continue
        readable, reason = readable_source(path)
        if not readable:
            stats_key = {
                'credential_path': 'skipped_credential_paths',
                'configuration_suffix': 'skipped_configuration_files',
                'non_text_suffix': 'skipped_non_text_files',
            }[reason]
            stats[stats_key] += 1
            continue
        try:
            data = path.read_bytes()
        except OSError:
            stats['failed_reads'] += 1
            continue
        if b'\0' in data[:4096]:
            stats['skipped_nul_binary_files'] += 1
            continue
        try:
            text = data.decode('utf-8')
        except UnicodeDecodeError:
            stats['non_utf8_reads'] += 1
            continue
        stats['scanned_utf8_text_files'] += 1
        category = source_class(name)
        for raw in REFERENCE_RE.findall(text):
            target = clean_target(raw)
            if target:
                found[category].add((name, target))
    return {
        category: [
            {'source': source, 'target': target}
            for source, target in sorted(items)
        ]
        for category, items in found.items()
    }, stats


def references_for(run_path: str, references: dict[str, list[dict]]) -> dict[str, list[dict]]:
    result = {}
    prefix = run_path + '/'
    for category, items in references.items():
        result[category] = [
            item for item in items
            if item['target'] == run_path or item['target'].startswith(prefix)
        ]
    return result


def escape_label(value: str) -> str:
    return value.replace("\\", "\\\\").replace('[', '\\[').replace(']', '\\]')


def link_url(from_file: Path, target: Path) -> str:
    path = os.path.relpath(target, from_file.parent).replace(os.sep, '/')
    return quote(path, safe='/:@-._~')


def chronological_files(directory: Path) -> list[Path]:
    if directory.is_symlink() or not directory.is_dir():
        fail(f'missing or invalid research record directory: {directory}')
    files = [
        path for path in directory.glob('*.md')
        if path.is_file() and not path.is_symlink() and path.name != 'README.md'
    ]
    return sorted(files, key=lambda path: (path.name[:10] if DATE_RE.match(path.name) else '9999-99-99', path.name))


def make_index(root: Path, output: Path, directory_name: str, title: str) -> str:
    directory = root / 'research' / directory_name
    candidate_file = output / f'{directory_name}-index.md'
    intended_destination = directory / 'README.md'
    lines = [
        f'# {title}',
        '',
        'This chronological index is generated from the dated Markdown records. README files are navigation pages and are intentionally omitted.',
        '',
    ]
    for path in chronological_files(directory):
        label = escape_label(path.stem)
        lines.append(f'- [{label}]({link_url(intended_destination, path)})')
    if len(lines) == 4:
        lines.append('- No dated records found.')
    return "\n".join(lines) + "\n"


def manifest_relative_path(root: Path, value: object, label: str) -> str:
    if not isinstance(value, str) or not value or '\0' in value:
        fail(f'{label} must be a nonempty path string without NUL')
    path = lexical_path(root, value)
    reject_symlink_components(path, root)
    try:
        path.relative_to(root)
    except ValueError:
        fail(f'{label} is outside the repository root: {value}')
    if not path.exists():
        fail(f'{label} does not exist: {value}')
    return relative(root, path)


def load_retention_manifest(root: Path, argument: str) -> list[dict]:
    manifest_path = lexical_path(root, argument)
    reject_symlink_components(manifest_path, root)
    if not manifest_path.is_file():
        fail(f'retention manifest is not a regular file: {manifest_path}')
    try:
        document = json.loads(manifest_path.read_text(encoding='utf-8'))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        fail(f'cannot read retention manifest: {exc}')
    if not isinstance(document, dict) or document.get('schema') != 1:
        fail('retention manifest schema must be exactly 1')
    manifest_root = document.get('root')
    if not isinstance(manifest_root, str):
        fail('retention manifest must contain a root string')
    declared_root = lexical_path(root, manifest_root)
    if declared_root != root:
        fail(f'retention manifest root does not match repository root: {manifest_root}')
    records = document.get('records')
    if not isinstance(records, list):
        fail('retention manifest records must be a list')
    result = []
    seen = set()
    for index, record in enumerate(records):
        if not isinstance(record, dict):
            fail(f'retention record {index} is not an object')
        path = manifest_relative_path(root, record.get('path'), f'retention record {index} path')
        if not (path == 'build/reviews' or path.startswith('build/reviews/') or path == 'build/verification' or path.startswith('build/verification/')):
            fail(f'retention record {index} path is outside inventory areas: {path}')
        if path in seen:
            fail(f'duplicate retention record path: {path}')
        seen.add(path)
        roles = record.get('roles')
        if not isinstance(roles, list) or not roles or any(not isinstance(role, str) for role in roles):
            fail(f'retention record {index} roles must be a nonempty list of strings')
        if any(role not in RETENTION_ROLES for role in roles):
            fail(f'retention record {index} contains an unrecognized role')
        source_evidence = record.get('source_evidence', record.get('evidence'))
        if not isinstance(source_evidence, list) or not source_evidence or any(not isinstance(item, str) or not item or '\0' in item for item in source_evidence):
            fail(f'retention record {index} requires nonempty exact source evidence strings')
        result.append({
            'path': path,
            'roles': sorted(set(roles)),
            'source_evidence': list(source_evidence),
        })
    return sorted(result, key=lambda record: record['path'])


def retention_for(path: str, records: list[dict]) -> dict:
    matches = [record for record in records if path == record['path'] or path.startswith(record['path'] + '/')]
    if not matches:
        return {
            'assessment': 'unknown',
            'roles': [],
            'source_evidence': [],
            'proof_coverage': False,
            'deletion_authorized': False,
        }
    roles = sorted({role for record in matches for role in record['roles']})
    evidence = sorted({item for record in matches for item in record['source_evidence']})
    return {
        'assessment': 'explicit_reviewed_roles_only',
        'roles': roles,
        'source_evidence': evidence,
        'proof_coverage': False,
        'deletion_authorized': False,
    }


def attach_retention(areas: dict[str, list[dict]], records: list[dict]) -> None:
    for runs in areas.values():
        for run in runs:
            run['retention'] = retention_for(run['path'], records)
            for artifact in run['artifacts']:
                artifact['retention'] = retention_for(artifact['path'], records)


def main() -> int:
    parser = argparse.ArgumentParser(description='Inventory evidence runs and generate ignored research-index candidates.')
    parser.add_argument('--root', default='.', help='repository root')
    parser.add_argument('--output', default='build/file-management', help='ignored output directory under build/')
    parser.add_argument('--retention-manifest', default=None, help='optional reviewed retention-role manifest')
    args = parser.parse_args()

    root = Path(args.root).resolve()
    if not (root / 'AGENTS.md').is_file():
        fail(f'repository root is not recognized: {root}')

    output_lexical = lexical_path(root, args.output)
    build_lexical = root / 'build'
    try:
        output_lexical.relative_to(build_lexical)
    except ValueError:
        fail(f'output must be under the ignored build directory: {output_lexical}')
    reject_symlink_components(output_lexical, root)
    for forbidden in (root / 'build' / 'reviews', root / 'build' / 'verification'):
        try:
            output_lexical.relative_to(forbidden)
        except ValueError:
            continue
        fail('output must not be inside an evidence run tree')
    output = output_lexical.resolve(strict=False)
    if output.exists() and not output.is_dir():
        fail(f'output is not a directory: {output}')

    reviews = list_runs(root, 'build/reviews')
    verification = list_runs(root, 'build/verification')
    references, reference_stats = reference_scan(root)
    for run in reviews + verification:
        run['references'] = references_for(run['path'], references)

    retention_records = []
    if args.retention_manifest is not None:
        retention_records = load_retention_manifest(root, args.retention_manifest)
    areas = {
        'build/reviews': reviews,
        'build/verification': verification,
    }
    attach_retention(areas, retention_records)

    output.mkdir(parents=True, exist_ok=True)
    payload = {
        'schema': 2,
        'logical_bytes_note': 'logical file sizes from stat; physical storage and savings are not measured',
        'coverage_note': 'artifact enumeration covers regular files under listed evidence runs only; skipped trees, symlinks, failed stats, ignored consumers, credentials, configurations, nonUTF8 sources, and physical storage are not claimed covered',
        'traversal_policy': 'symlinks, nested .lake, .git, and node_modules are skipped and counted separately',
        'reference_policy': 'git-tracked and nonignored UTF-8 source/documentation text only; credential paths, configuration suffixes, binary/NUL files, failed reads, nonUTF8 files, and ignored consumers are excluded',
        'reference_exclusions': reference_stats,
        'ignored_consumers_exclusion': 'not enumerated because git ls-files uses --exclude-standard',
        'physical_space_exclusion': 'not measured',
        'retention_policy': {
            'manifest_schema': 1,
            'roles': sorted(RETENTION_ROLES),
            'requires_explicit_reviewed_source_evidence': True,
            'unclassified_assessment': 'unknown',
            'proof_coverage_declared': False,
            'deletion_authorized': False,
            'tool_artifact_mode': 'read_only',
        },
        'retention_manifest_records': retention_records,
        'index_candidates': [
            {
                'candidate_path': relative(root, output / 'decisions-index.md'),
                'intended_destination': 'research/decisions/README.md',
                'link_base': 'research/decisions/README.md',
            },
            {
                'candidate_path': relative(root, output / 'handoffs-index.md'),
                'intended_destination': 'research/handoffs/README.md',
                'link_base': 'research/handoffs/README.md',
            },
        ],
        'areas': areas,
        'all_references': references,
    }
    (output / 'inventory.json').write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding='utf-8')
    (output / 'decisions-index.md').write_text(make_index(root, output, 'decisions', 'Chronological decision-record index'), encoding='utf-8')
    (output / 'handoffs-index.md').write_text(make_index(root, output, 'handoffs', 'Chronological handoff index'), encoding='utf-8')
    print(f'wrote ignored inventory candidates to {output}')
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except RuntimeError as exc:
        print(f'error: {exc}', file=sys.stderr)
        raise SystemExit(2)
