"""Build round-two report and frozen artifact inventory from exact archives."""
import hashlib
import json
from pathlib import Path

BASE=Path(__file__).resolve().parents[1]
V=BASE/'verification'


def index(name):
    return [json.loads(line) for line in (V/name).read_text(encoding='utf-8').splitlines()]


def main():
    atoms=index('elimination-atoms.jsonl')
    combos=index('elimination-results.jsonl')
    audit=json.loads((V/'elimination-audit.json').read_text(encoding='utf-8'))
    assert len(atoms)==160 and len(combos)==63
    assert all(row['status']=='ok' for row in atoms+combos)
    assert sum(row['below_one'] for row in atoms)==49
    assert not any(row['below_one'] for row in combos)
    assert audit['all_exact_scales_and_cofactors_verified']
    assert audit['all_signed_arb_balls_rechecked']
    canonical=[]
    rows=[]
    for n in (12,24,48):
        atom=next(r for r in atoms if r['p']==9 and r['n']==n and r['m']==n)
        combo=next(r for r in combos if r['p']==9 and r['n']==n and r['m_start']==n)
        canonical.append(dict(n=n,atom_score=atom['abs_log_per_n'],combination_score=combo['abs_log_per_n']))
        rows.append(f"| {n} | {atom['abs_log_per_n']:.6f} | {combo['abs_log_per_n']:.6f} |")
    promoted=[]
    for last in sorted((r for r in combos if r['n']==96),key=lambda r:r['p']):
        prev=next(r for r in combos if r['p']==last['p'] and r['n']==48
                  and r['profile_slot']==last['profile_slot'])
        promoted.append(f"| p={last['p']}，n=96 时 m={last['m_values']} | "
                        f"{prev['abs_log_per_n']:.6f} | {last['abs_log_per_n']:.6f} |")
    template=(BASE/'research/report-template.md').read_text(encoding='utf-8')
    report=template.replace('{{CANONICAL}}','\n'.join(rows)).replace('{{PROMOTED}}','\n'.join(promoted))
    (BASE/'report.md').write_text(report,encoding='utf-8')
    summary=dict(status='round2_complete_no_single_zeta9_proof',date='2026-09-24',
                 atom_count=160,atom_below_one=49,combination_count=63,
                 combination_below_one=0,timeouts=0,degenerate_combinations=0,
                 initial_grid=58,canonical_windows=3,promoted_n96=2,
                 canonical=canonical,
                 proved_multi_zeta_decay='0<d_n^9 L_n<=exp((-1.43+o(1))*n)',
                 support=[1,3,5,7,9],
                 unproved='nonzero decay after isolating zeta9',
                 future_seed='fixed weights (-7776,1701,-224,1); conditional algebra only')
    (V/'summary.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
    files=sorted(p for p in BASE.rglob('*') if p.is_file() and '__pycache__' not in p.parts
                 and p.name!='artifact-manifest.json')
    manifest=[dict(path=p.relative_to(BASE).as_posix(),bytes=p.stat().st_size,
                   sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in files]
    (V/'artifact-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(files=len(files),report=str(BASE/'report.md'),atom_count=len(atoms),combinations=len(combos))))


if __name__=='__main__':
    main()
