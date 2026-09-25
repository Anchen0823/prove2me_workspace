"""Replay saved global comparison certificate at higher Arb precision.

Reads the rational measure and partition from the certificate, not the
floating-point exploratory output. Rechecks exact coverage and all bounds.
"""
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from round2_energy_certificate import (
    ROOT, OUTPUT, EPS, TAIL_T, LAM, GAMMA, LAYERS, TARGET,
    a, ctx, upper_middle, small_tail, large_tail, energy_and_constant, serial)


def fraction(obj):
    return Fraction(int(obj['numerator']),int(obj['denominator']))


def main():
    data=json.loads(OUTPUT.read_text(encoding='utf-8'))
    arcs=[tuple(fraction(x[k]) for k in ('left','right','weight')) for x in data['arcs']]
    assert fraction(data['lambda_mass'])==LAM
    assert fraction(data['gamma'])==GAMMA
    assert tuple((fraction(x['alpha']),x['q']) for x in data['layers'])==LAYERS
    assert fraction(data['epsilon'])==EPS and fraction(data['T'])==TAIL_T
    assert fraction(data['target_M'])==TARGET
    assert all(EPS<l<r<TAIL_T and c>0 for l,r,c in arcs)
    assert sum(c for l,r,c in arcs)==LAM
    assert all(arcs[i][0]>arcs[i+1][0] and arcs[i][1]<arcs[i+1][1] for i in range(len(arcs)-1))
    intervals=sorted((fraction(x['lo']),fraction(x['hi'])) for x in data['middle_intervals'])
    assert intervals[0][0]==EPS and intervals[-1][1]==TAIL_T
    assert all(l<r for l,r in intervals)
    assert all(intervals[i][1]==intervals[i+1][0] for i in range(len(intervals)-1))
    with ctx.workprec(256):
        small=small_tail(arcs)
        large,D,C=large_tail()
        assert small.upper()<a(TARGET) and large.upper()<a(TARGET)
        for lo,hi in intervals:
            bound=upper_middle(lo,hi,arcs)
            assert bound is not None and bound[0].upper()<a(TARGET)
        I,Cstar,U=energy_and_constant(arcs)
        assert U.upper()<a(Fraction(507,1000))
        result=dict(verified=True,precision_bits=256,intervals_checked=len(intervals),
                    exact_partition_coverage=True,exact_positive_mass_and_nesting=True,
                    both_infinite_tails_checked=True,global_target_M=str(TARGET),
                    energy_I=serial(I),Cstar=serial(Cstar),U_bound=serial(U),
                    certificate_sha256=hashlib.sha256(OUTPUT.read_bytes()).hexdigest(),
                    checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                    boundary='Global comparison-potential bound; no arithmetic asymptotic and no irrationality claim.')
    (ROOT/'missions/zeta7/verification/round2-energy-replay.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
