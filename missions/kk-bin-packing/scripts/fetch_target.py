"""Fetch the selected public target and its actual platform imports; never submit."""
import http.client
import json
from pathlib import Path
import re
import sys
from urllib.parse import urlencode

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'scripts'))
import p2m_api as api

HERE = ROOT / 'missions/kk-bin-packing'
TARGET = '641936bb-5a63-4aa2-9352-d96c0186cb3f'


def main():
    token = api.get_token()

    def get(path):
        try:
            status, body = api._request('GET', path, token=token)
        except http.client.IncompleteRead as exc:
            status, body = 200, exc.partial.decode('utf-8')
        if status != 200:
            raise RuntimeError(f'GET {path}: {status}')
        return json.loads(body)

    target = get('/theorems/' + TARGET)
    (HERE / 'verification/target-before.json').write_text(json.dumps(target, ensure_ascii=False, indent=2), encoding='utf-8')
    filename = 'Theorems/Thm_' + target['theorem_name'].replace('.', '_') + '.lean'
    files = [filename]
    (ROOT / filename).write_text(target['preamble'] + '\n\n' + target['formal_statement'], encoding='utf-8')
    seen = set()

    def imports(source):
        for module in re.findall(r'^import ((?:Definitions|Theorems)\.[\w.]+)', source, re.M):
            if module in seen:
                continue
            seen.add(module)
            kind, name = module.split('.', 1)
            if kind != 'Definitions':
                raise RuntimeError('Unexpected theorem dependency: ' + module)
            name = name.removeprefix('Def_')
            data = get('/theorems?' + urlencode({'theorem_name': name, 'env': target['mathlib_rev']}))
            nodes = data['theorems']
            if len(nodes) != 1 or nodes[0]['status'] != 'Definition':
                raise RuntimeError('Definition lookup failed: ' + name)
            node = nodes[0]
            source = node['definition']
            path = module.replace('.', '/') + '.lean'
            dest = ROOT / path
            if dest.exists() and dest.read_text(encoding='utf-8') != source:
                raise RuntimeError('Refusing to overwrite existing different file: ' + path)
            dest.write_text(source, encoding='utf-8')
            files.append(path)
            (HERE / ('verification/definition-' + name + '.json')).write_text(json.dumps(node, ensure_ascii=False, indent=2), encoding='utf-8')
            print(path, flush=True)
            imports(source)

    imports(target['preamble'])
    scope = json.loads((HERE / 'scope.json').read_text(encoding='utf-8'))
    scope['sources'] = sorted(set(scope['sources'] + files))
    (HERE / 'scope.json').write_text(json.dumps(scope, indent=2) + '\n', encoding='utf-8')


if __name__ == '__main__':
    main()
