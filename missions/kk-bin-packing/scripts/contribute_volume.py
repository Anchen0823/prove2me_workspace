"""Explicit, recorded API actions for the Lemma 2 contribution.

Usage: get PATH LABEL | poll | publish PAYLOAD LABEL | submit THEOREM_ID SOURCE EXPLANATION LABEL
Mutating commands refuse to repeat a request with a saved response/attempt.
"""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'scripts'))
import p2m_api as api

OUT = ROOT / 'missions/kk-bin-packing/verification/volume-2026-10-02'

def save(label, value):
    (OUT / (label + '.json')).write_text(
        json.dumps(value, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')

def request(method, path, label, **kwargs):
    status, body = api._request(method, path, token=api.get_token(), **kwargs)
    try:
        value = json.loads(body)
    except json.JSONDecodeError:
        value = {'unparsed_response': body}
    save(label, value)
    print(json.dumps({'http_status': status, 'result': value}, ensure_ascii=True))
    if status >= 400:
        raise SystemExit(1)

def main():
    OUT.mkdir(parents=True, exist_ok=True)
    mode = sys.argv[1]
    if mode == 'get':
        request('GET', sys.argv[2], sys.argv[3])
    elif mode == 'poll':
        targets = []
        for label in ['lower', 'parent']:
            response = OUT / (label + '-submit-response.json')
            if response.exists():
                sid = json.loads(response.read_text(encoding='utf-8'))['submission_id']
                targets.append((label + '-verdict', '/verify?submission_id=' + sid))
        core_response = OUT / 'cores-publish-retry1-response.json'
        if core_response.exists():
            for job in json.loads(core_response.read_text(encoding='utf-8'))['jobs']:
                label = 'sparse' if job['name'].endswith('exists_sparse_near_optimal_lp') else 'rounding'
                targets.append((label + '-publish-job', '/publish-jobs/' + job['job_id']))
        token = api.get_token()
        for label, path in targets:
            status, body = api._request('GET', path, token=token)
            if status != 200:
                raise RuntimeError(f'{label}: HTTP {status}: {body[:300]}')
            value = json.loads(body)
            save(label, value)
            print(json.dumps({'name': label, 'status': value.get('status'),
                              'id': value.get('id'), 'theorem_id': value.get('theorem_id'),
                              'error': value.get('error_message')}, ensure_ascii=True), flush=True)
    elif mode == 'publish':
        payload_name, label = sys.argv[2:]
        if (OUT / (label + '-attempt.json')).exists():
            raise SystemExit('Publish already attempted; inspect the saved response before retrying.')
        payload = json.loads((OUT / payload_name).read_text(encoding='utf-8'))
        save(label + '-attempt', payload)
        request('POST', '/submit-problem', label + '-response', data=payload)
    elif mode == 'submit':
        theorem_id, source_path, explanation_path, label = sys.argv[2:]
        if (OUT / (label + '-attempt.json')).exists():
            raise SystemExit('Submission already attempted; inspect evidence before retrying.')
        source = (ROOT / source_path).read_text(encoding='utf-8')
        explanation = (ROOT / explanation_path).read_text(encoding='utf-8')
        save(label + '-attempt', {
            'theorem_id': theorem_id, 'source_path': source_path,
            'source_sha256': hashlib.sha256(source.encode()).hexdigest(),
            'explanation_path': explanation_path,
        })
        body, ctype = api._multipart(
            {'theorem_id': theorem_id, 'proof_type': 'prove', 'explanation': explanation},
            {'file': ('solution.lean', source)},
        )
        request('POST', '/verify', label + '-response', raw_body=body, ctype=ctype)
    else:
        raise SystemExit('Unknown action: ' + mode)

if __name__ == '__main__':
    main()
