"""Read current evidence for the Lemma 2 contribution; never publish or submit."""
import concurrent.futures
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'scripts'))
import p2m_api as api

OUT = ROOT / 'missions/kk-bin-packing/verification/volume-2026-10-02'
TARGET = '5455998b-e4e9-4edb-92fc-4effa3b071a2'
PATHS = {
    'target-before': '/theorems/' + TARGET,
    'decompositions-before': '/theorems/' + TARGET + '/decompositions',
    'submissions-before': '/theorems/' + TARGET + '/submissions',
    'mentions-before': '/theorems/' + TARGET + '/mentions',
    'history': '/milestones/8f8526d0-209c-40d6-be79-f5de0d804c3d/history',
    'comments-before': '/missions/359adb44-9a24-441c-8a2b-bd71395fcad4/comments',
    'lower-search': '/theorems?theorem_name=KKBinPacking.GeometricGrouping.size_le_lin',
    'upper-search': '/theorems?theorem_name=KKBinPacking.GeometricGrouping.opt_le_lin_add',
    'linear-lower': '/theorems/555b051c-6aa5-4769-866f-a595b8c60e2c',
}

def main():
    OUT.mkdir(parents=True, exist_ok=True)
    token = api.get_token()
    def fetch(item):
        name, path = item
        status, body = api._request('GET', path, token=token)
        if status != 200:
            raise RuntimeError(f'{name}: HTTP {status}: {body[:500]}')
        value = json.loads(body)
        (OUT / (name + '.json')).write_text(json.dumps(value, indent=2, ensure_ascii=False), encoding='utf-8')
        return name, value
    with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
        for name, value in pool.map(fetch, PATHS.items()):
            print(json.dumps({'name': name, 'result': value}, ensure_ascii=True))

if __name__ == '__main__':
    main()
