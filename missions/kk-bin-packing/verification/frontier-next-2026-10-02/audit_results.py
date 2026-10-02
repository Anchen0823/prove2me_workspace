"""Read server verdicts, verify stored source hashes, and record the current frontier."""
import hashlib
import json
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'scripts'))
import p2m_api as api

token = api.get_token()
def get(path, name):
    for attempt in range(4):
        try:
            status, body = api._request('GET', path, token=token)
            if status != 200:
                raise RuntimeError('HTTP ' + str(status))
            data = json.loads(body)
            (HERE / (name + '.json')).write_text(body, encoding='utf-8')
            return data
        except Exception:
            if attempt == 3:
                raise
            time.sleep(2)

def normalized(source):
    return source.replace('\r\n', '\n')

results = []
for short, suffix in [('telescoping', 'alg2_lin_telescoping'),
                      ('dominance', 'geom_dominance_certificate'),
                      ('lp-monotone', 'lin_mono_submultiset')]:
    submit_path = HERE / (short + '-submit.json')
    if not submit_path.exists():
        results.append({'name': short, 'status': 'awaiting theorem publication'})
        continue
    submission = json.loads(submit_path.read_text(encoding='utf-8'))['submission_id']
    verdict = get('/verify?submission_id=' + submission, short + '-verdict')
    row = {'name': suffix, 'submission_id': submission, 'theorem_id': verdict['theorem_id'],
           'status': verdict['status'], 'updated_at': verdict.get('updated_at')}
    source_path = 'Solutions/Sol_KKBinPacking_GeometricGrouping_' + suffix + '.lean'
    local_source = normalized((ROOT / source_path).read_text(encoding='utf-8'))
    row['source'] = source_path
    row['sha256'] = hashlib.sha256(local_source.encode('utf-8')).hexdigest()
    if verdict['status'] in ('ACCEPTED', 'SKETCH_ACCEPTED'):
        remote = get('/submissions/' + submission + '/solution', short + '-remote-source')['content']
        row['server_source_matches_local'] = normalized(remote) == local_source
        if not row['server_source_matches_local']:
            raise SystemExit('Stored source mismatch: ' + short)
        theorem = get('/theorems/' + verdict['theorem_id'], short + '-after')
        row['theorem_status'] = theorem['status']
        if verdict['status'] == 'ACCEPTED':
            get('/theorems/' + verdict['theorem_id'] + '/submissions?first=true', short + '-first-accepted')
    results.append(row)
frontier = get('/theorems/4f2723e6-02fb-41ff-9cf9-af6f1d0fc02b/open-leaves', 'frontier-after')
(HERE / 'final-results.json').write_text(json.dumps({'submissions': results, 'open_frontier': frontier},
                                                   ensure_ascii=False, indent=2), encoding='utf-8')
print(json.dumps({'results': results, 'open_leaves': frontier['total']}, ensure_ascii=True), flush=True)
