"""Generate kernel-checked LCM certificates; Python is not a trusted prover."""
import argparse
import math
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("--limit", type=int, default=1000)
parser.add_argument("--output", type=Path, required=True)
parser.add_argument("--reuse-blocks", action="store_true")
parser.add_argument("--adaptive-powers", action="store_true")
parser.add_argument("--reuse-critical-proof", action="store_true")
args = parser.parse_args()
if not 1 <= args.limit <= 1000:
    raise ValueError("This prototype is bounded to 1..1000")

lcms = [1]
for n in range(1, args.limit + 1):
    lcms.append(math.lcm(lcms[-1], n))
blocks = []
a = 1
while a <= args.limit:
    if lcms[a].bit_length() * 693147181 >= 1038830000 * a:
        d = 1 if args.adaptive_powers else 1000
        if args.adaptive_powers:
            while (lcms[a] ** d).bit_length() * 693147181 >= 1038830000 * a * d:
                d *= 2
                if d > 1024:
                    raise ValueError(f"Insufficient adaptive precision at {a}")
        k = (lcms[a] ** d).bit_length()
        if k * 693147181 >= 1038830000 * a * d:
            raise ValueError(f"Insufficient precision at {a}")
        blocks.append((a, a, d, k))
        a += 1
        continue
    b = a
    while b < args.limit and lcms[b + 1].bit_length() * 693147181 < 1038830000 * a:
        b += 1
    blocks.append((a, b, 1, lcms[b].bit_length()))
    a = b + 1

lines = [
    'import examples.«five-primes».' + ('RosserLcmBlocks' if args.reuse_blocks else 'RosserLcmCertificate'),
    '', 'namespace TaoFivePrimes', '',
    'set_option maxRecDepth 16384',
    'set_option maxHeartbeats 4000000',
    'set_option exponentiation.threshold 200000', '',
]
if args.reuse_critical_proof:
    lines.insert(1, 'import examples.«five-primes».RosserCriticalEndpoint')
if args.reuse_blocks:
    previous = 0
    for _, b, _, _ in blocks:
        lines.extend([
            f'private theorem lcm_value_{b} : Nat.lcmUpto {b} = {lcms[b]} := by',
            f'  apply lcmUpto_eq_of_block {previous} {b} {lcms[previous]} {lcms[b]} (by omega)',
            '  · ' + ('decide' if previous == 0 else f'exact lcm_value_{previous}'),
            '  · decide', '',
        ])
        previous = b
lines.extend([
    '/-- Generated integer certificates, all checked by the Lean kernel. -/',
    f'theorem rosser_up_to_{args.limit} (n : ℕ) (hn : 0 < n) (hN : n ≤ {args.limit}) :',
    '    Chebyshev.psi (n : ℝ) < 1.03883 * (n : ℝ) := by',
    '  have hcover : ' + ' ∨ '.join(f'({a} ≤ n ∧ n ≤ {b})' for a,b,_,_ in blocks) + ' := by omega',
    '  rcases hcover with ' + ' | '.join('h' for _ in blocks),
])
for a,b,d,k in blocks:
    check = f'(by rw [lcm_value_{b}]; decide)' if args.reuse_blocks else '(by decide)'
    if args.reuse_critical_proof and a == b == 113:
        lines.extend([
            '  · have heq : n = 113 := by omega',
            '    subst n',
            '    exact rosser_at_113',
        ])
    elif d == 1:
        lines.extend([
            f'  · exact rosser_interval_of_power {a} {b} {k} {check} (by norm_num)',
            '      n (by exact_mod_cast h.1) (by exact_mod_cast h.2)',
        ])
    else:
        lines.extend([
            f'  · have heq : n = {a} := by omega',
            '    subst n',
            f'    have hp := psi_mul_le_of_lcm_power {a} {d} {k} {check}',
            '    norm_num at hp ⊢',
            '    linarith',
        ])
lines.extend(['', 'end TaoFivePrimes', ''])
args.output.write_text('\n'.join(lines), encoding='utf-8')
print(f'Generated {len(blocks)} blocks covering 1..{args.limit}; Lean validation required.')
