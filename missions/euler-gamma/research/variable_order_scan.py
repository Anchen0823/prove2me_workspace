"""Exact-rational exploration, not a proof of irrationality or novelty.

Family motivated by Van Assche--Wolfs, arXiv:2404.09799v3 section 5.
At p=2 the formulas equal the current Prove2Me P2 definition.
Gamma enclosure uses Euler--Maclaurin's signed next-term remainder and
the positive atanh series for log(2), all computed with Fraction.
Only the logarithmic display columns use floating point.
"""
from fractions import Fraction as F
from math import comb, factorial, log10
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent

def harmonic_list(n):
    h = [F(0)]
    for k in range(1, n+1):
        h.append(h[-1]+F(1,k))
    return h

def gamma_interval():
    m, s, terms = 1024, 40, 256
    # Bernoulli recurrence; B_1=-1/2, only even indices used below.
    b = [F(1)]
    for j in range(1, 2*s+3):
        b.append(-sum((F(comb(j+1,k))*b[k] for k in range(j)), F(0))/(j+1))
    log2_lo = 2*sum((F(1,(2*j+1)*3**(2*j+1)) for j in range(terms)), F(0))
    log2_hi = log2_lo + 2*F(1,3**(2*terms+1))*F(9,8)/ (2*terms+1)
    a = harmonic_list(m)[-1]-F(1,2*m)
    a += sum((b[2*k]/(2*k*m**(2*k)) for k in range(1,s+1)), F(0))
    next_term = b[2*s+2]/((2*s+2)*m**(2*s+2))
    return a-10*log2_hi+min(F(0),next_term), a-10*log2_lo+max(F(0),next_term)

def lg(x):
    assert x > 0
    return log10(x.numerator)-log10(x.denominator)

def approximant(n,p,h):
    q, numerator = F(0), F(0)
    for k in range(n+1):
        c = F(comb(n,k)**2 * comb(n+k,k)**p, factorial(k))
        q += c
        numerator -= c*(p*h[n+k]+2*h[n-k]-(p+3)*h[k])
    assert q > 0
    assert numerator <= (3*h[n]-F(p,2))*q
    return numerator/q

def main():
    low, high = gamma_interval()
    assert F(5772156649015328606,10**19) < low < high < F(5772156649015328607,10**19)
    ns = list(range(1,257))
    hs = harmonic_list(2*max(ns))
    rows = []
    for n in ns:
        cutoff = 6*hs[n]
        first_excluded = (cutoff.numerator+cutoff.denominator-1)//cutoff.denominator
        for p in range(first_excluded):
            r = approximant(n,p,hs)
            a, b = r.denominator, r.numerator
            l, u = a*low-b, a*high-b
            if l <= 0 <= u:
                raise RuntimeError('Gamma enclosure too wide to certify this sign')
            amin, amax = sorted((abs(l),abs(u)))
            rows.append(dict(n=n,p=p,log10_denominator=log10(a),
                approx_log10_abs_linear_form=lg((amin+amax)/2),
                log10_absolute_error_upper=lg(amax/F(a)),
                numerator_nonpositive=b<=0,large_order_excluded=F(p)>=6*hs[n],
                primitive_abs_form_lt_one=amax<1,
                primitive_abs_form_gt_one=amin>1,
                primitive_abs_form_lt_half=amax<F(1,2)))
    # Directed graph audit includes sketch and definition nodes, not only theorem names.
    graph=json.loads((HERE/'graph.json').read_text(encoding='utf-8-sig'))
    adj={}
    for edge in graph['edges']:
        adj.setdefault(edge['source'],[]).append(edge['target'])
    active,done=set(),set()
    def visit(v):
        if v in active: raise RuntimeError('Cycle in retrieved graph')
        if v in done: return
        active.add(v)
        for w in adj.get(v,[]): visit(w)
        active.remove(v); done.add(v)
    for v in adj: visit(v)
    summary=dict(samples=len(rows),n_range=[1,256],p_rule='0 <= p < ceil(6 H_n); all larger orders excluded analytically by the proved bound',
        gamma_interval_log10_width=lg(high-low),
        certified_signs=len(rows),retrieved_graph_acyclic=True,
        graph_node_count=len(graph['nodes']),graph_edge_count=len(graph['edges']),
        graph_has_truncated_nodes=any(x.get('has_more_children') or x.get('has_more_parents') for x in graph['nodes']),
        best_per_large_n=[min((r for r in rows if r['n']==n),key=lambda r:r['approx_log10_abs_linear_form']) for n in [32,48,64,96,128,192,256]],
        cases_below_one=[r for r in rows if r['primitive_abs_form_lt_one']],
        all_scanned_forms_gt_one_from_n_8=all(r['primitive_abs_form_gt_one'] for r in rows if r['n']>=8),
        limitation='Finite exact-rational parameter scan; no infinite-subsequence conclusion. Gamma enclosure theorem is used on paper, not yet formalized in Lean.')
    (HERE/'variable-order-results.json').write_text(json.dumps(dict(summary=summary,rows=rows),indent=2))
    (HERE/'gamma-enclosure.json').write_text(json.dumps(dict(lower=[str(low.numerator),str(low.denominator)],upper=[str(high.numerator),str(high.denominator)])))
    print(json.dumps(summary,indent=2))

if __name__ == '__main__': main()
