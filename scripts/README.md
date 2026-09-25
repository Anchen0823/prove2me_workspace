# Shared tools

- `p2m_api.py`: platform API client (some commands perform writes).
- `extract_decl_graph.lean`, `extract_sketch_info.lean`: Lean inspection tools.
- `workspace.py`: offline mission navigation and layout validation.

Mission-specific scripts are under `missions/<slug>/scripts/`.
Run `python scripts/workspace.py show <slug>` to find them.
See [the migration map](../docs/script-migration.json) for previous paths.
