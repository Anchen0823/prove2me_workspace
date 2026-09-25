"""Offline mission navigation and structural checks; never submits proofs."""
import argparse
import ast
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def inside_root(value):
    path = (ROOT / value).resolve()
    if not path.is_relative_to(ROOT):
        raise ValueError(f'Path outside workspace: {value}')
    return path


def check(missions):
    errors = []
    slugs = [m['slug'] for m in missions]
    if len(slugs) != len(set(slugs)):
        errors.append('Duplicate mission slugs')
    actual = {p.name for p in (ROOT / 'missions').iterdir()
              if p.is_dir() and not p.name.startswith('_')}
    if actual != set(slugs):
        errors.append(f'Registry/directory mismatch: {sorted(actual ^ set(slugs))}')
    for m in missions:
        for key in ('handoff', 'scratch'):
            if m.get(key) and not inside_root(m[key]).exists():
                errors.append(f"Missing {key}: {m[key]}")
        if f"({m['handoff'].removeprefix('missions/')})" not in (ROOT / 'missions/README.md').read_text(encoding='utf-8'):
            errors.append(f"Missing README handoff: {m['slug']}")
    moves = json.loads((ROOT / 'docs/script-migration.json').read_text(encoding='utf-8'))['moves']
    for move in moves:
        if not inside_root(move['to']).is_file() or inside_root(move['from']).exists():
            errors.append(f"Incomplete migration: {move['from']}")
    sources = list((ROOT / 'scripts').glob('*.py'))
    sources += list((ROOT / 'missions').glob('*/scripts/*.py'))
    for path in sources:
        try:
            ast.parse(path.read_text(encoding='utf-8-sig'), filename=str(path))
        except SyntaxError as exc:
            errors.append(str(exc))
    for error in errors:
        print(f'ERROR: {error}')
    if not errors:
        print(f'OK: {len(missions)} workstreams, {len(moves)} moved scripts, {len(sources)} Python files parsed.')
    return bool(errors)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    commands.add_parser('list')
    show = commands.add_parser('show')
    show.add_argument('slug')
    commands.add_parser('check')
    args = parser.parse_args()
    missions = json.loads((ROOT / 'missions/index.json').read_text(encoding='utf-8'))['missions']
    if args.command == 'check':
        return check(missions)
    if args.command == 'list':
        for m in missions:
            print(f"{m['slug']:25} {m['family']:15} {m['title']}")
        return 0
    m = next((m for m in missions if m['slug'] == args.slug), None)
    if m is None:
        parser.error(f'Unknown mission: {args.slug}')
    print(m['title'])
    print(f"Handoff: {m['handoff']}")
    print(f"Scratch: {m.get('scratch') or '(see handoff)'}")
    print('Scripts (inspect before running; some perform platform writes):')
    for path in sorted((ROOT / 'missions' / m['slug'] / 'scripts').glob('*')):
        if path.is_file():
            print(f'  {path.relative_to(ROOT).as_posix()}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
