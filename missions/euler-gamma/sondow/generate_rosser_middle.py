"""Exact certificate generator. Lean checks arithmetic and coverage independently."""
import argparse
import json
import math
import sys
from pathlib import Path

sys.set_int_max_str_digits(0)
p = argparse.ArgumentParser()
p.add_argument('--limit', type=int, default=10000)
p.add_argument('--output', type=Path, required=True)
p.add_argument('--numeral-format', choices=('hex', 'decimal'), default='hex')
p.add_argument('--balanced', action='store_true', help='Use the proved balanced LCM evaluator')
p.add_argument('--kernel', action='store_true', help='Use direct kernel reduction with cached auxiliary lemmas')
p.add_argument('--certificate-tree', action='store_true', help='Certify small interval values separately before merging')
p.add_argument('--compact', action='store_true', help='Infer repeated numeric arguments in certificate-tree applications')
a = p.parse_args()
if a.balanced and a.certificate_tree:
    raise ValueError('Choose either a recursive evaluator or a tree of separate certificates.')
if a.compact and not a.certificate_tree:
    raise ValueError('--compact requires --certificate-tree.')
if not 1001 <= a.limit <= 1000000:
    raise ValueError('Validate scalability before increasing the supported range.')
# Only prime powers change lcm(1,...,i). This sieve is untrusted generation
# machinery: every resulting endpoint is independently checked by Lean.
prime = bytearray(b'\x01') * (a.limit + 1)
prime[0:2] = b'\x00\x00'
for q in range(2, math.isqrt(a.limit) + 1):
    if prime[q]:
        prime[q*q::q] = b'\x00' * ((a.limit-q*q)//q + 1)
events = {}
for q in range(2, a.limit + 1):
    if prime[q]:
        power = q
        while power <= a.limit:
            events[power] = q
            power *= q
values = {}
current = 1
for i in range(1, 1001):
    if i in events:
        current *= events[i]
values[1000] = current
blocks = []
lo = 1001
for i in range(1001, a.limit+1):
    candidate = current * events[i] if i in events else current
    if candidate.bit_length()*693147181 >= 1038830000*lo:
        if i == lo:
            raise ValueError(f'Power certificate too coarse at {lo}')
        values[i-1] = current
        blocks.append((lo, i-1, current.bit_length()))
        lo = i
        if candidate.bit_length()*693147181 >= 1038830000*lo:
            raise ValueError(f'Power certificate too coarse at {lo}')
    current = candidate
values[a.limit] = current
blocks.append((lo, a.limit, current.bit_length()))
numerals = {n: hex(v) if a.numeral_format == 'hex' else str(v)
            for n, v in values.items()}
certificate_import = ('Solutions.SondowLcmTreeCertificate' if a.certificate_tree else
                      'Solutions.SondowBalancedLcm' if a.balanced else
                      'examples.«five-primes».RosserLcmBlocks')
step = 'lcmUpto_eq_of_balanced_block 20' if a.balanced else 'lcmUpto_eq_of_block'
lines = [f'import {certificate_import}', '',
         'namespace EulerMascheroni.Sondow', 'open TaoFivePrimes',
         'set_option maxRecDepth 32768', 'set_option maxHeartbeats 4000000',
         f'set_option exponentiation.threshold {max(300000, 2*a.limit)}', '',
         f'private theorem lcm_1000 : Nat.lcmUpto 1000 = {numerals[1000]} := by decide', '']
prev = 1000
def numeral(value):
    return hex(value) if a.numeral_format == 'hex' else str(value)

def emit_interval(left, right):
    name = f'block_{left}_{right}'
    if right-left <= 128:
        value = math.lcm(*range(left+1, right+1))
        lines.extend([f'private theorem {name} : (Finset.Ioc {left} {right}).lcm id = {numeral(value)} := by decide', ''])
    else:
        middle = (left+right)//2
        ln, lv = emit_interval(left, middle)
        rn, rv = emit_interval(middle, right)
        value = math.lcm(lv, rv)
        split_lemma = ('intervalLcm_eq_of_split_compact' if a.compact else
                       'intervalLcm_eq_of_split')
        split_args = (f'{left} {middle} {right}' if a.compact else
                      f'{left} {middle} {right} {numeral(lv)} {numeral(rv)} {numeral(value)}')
        lines.extend([f'private theorem {name} : (Finset.Ioc {left} {right}).lcm id = {numeral(value)} := by',
            f'  exact {split_lemma} {split_args}',
            f'    (by omega) (by omega) {ln} {rn} (by decide)', ''])
    return name, value

for lo, hi, bits in blocks:
    if a.certificate_tree:
        block_name, block_value = emit_interval(prev, hi)
        prefix_lemma = ('lcmUpto_eq_of_certified_block_compact' if a.compact else
                       'lcmUpto_eq_of_certified_block')
        prefix_args = (f'{prev} {hi}' if a.compact else
                       f'{prev} {hi} {numerals[prev]} {numeral(block_value)} {numerals[hi]}')
        lines += [f'private theorem lcm_{hi} : Nat.lcmUpto {hi} = {numerals[hi]} := by',
                  f'  exact {prefix_lemma} {prefix_args}',
                  f'    (by omega) lcm_{prev} {block_name} (by decide)', '']
    else:
        lines += [f'private theorem lcm_{hi} : Nat.lcmUpto {hi} = {numerals[hi]} := by',
                  f'  exact {step} {prev} {hi} {numerals[prev]} {numerals[hi]}',
                  f'    (by omega) lcm_{prev} (by decide)', '']
    prev = hi
lines += [f'theorem rosser_middle_to_{a.limit} (n : ℕ) (hn : 1000 < n) (hN : n ≤ {a.limit}) :',
          '    Chebyshev.psi (n:ℝ) < 1.03883*(n:ℝ) := by']
def tree(start, end, indent):
    pad = ' '*indent
    if end-start == 1:
        lo, hi, bits = blocks[start]
        return [pad+f'exact rosser_interval_of_power {lo} {hi} {bits}',
                pad+f'  (by rw [lcm_{hi}]; decide) (by norm_num) n',
                pad+'  (by exact_mod_cast (show '+str(lo)+' ≤ n by omega))',
                pad+'  (by exact_mod_cast (show n ≤ '+str(hi)+' by omega))']
    mid = (start+end)//2
    bound = blocks[mid-1][1]
    result = [pad+f'by_cases h{bound} : n ≤ {bound}']
    for left, right in [(start, mid), (mid, end)]:
        child = tree(left, right, indent+2)
        result += [pad+'· '+child[0].lstrip()] + child[1:]
    return result
lines += tree(0, len(blocks), 2)
lines += ['', 'end EulerMascheroni.Sondow', '',
          f'#print axioms EulerMascheroni.Sondow.rosser_middle_to_{a.limit}', '']
if a.kernel:
    lines = [line.replace('by decide', 'by decide +kernel').replace('; decide)', '; decide +kernel)')
             for line in lines]
a.output.write_text('\n'.join(lines), encoding='utf-8')
a.output.with_suffix('.json').write_text(json.dumps({'limit': a.limit, 'blocks': blocks,
    'numeral_format': a.numeral_format,
    'balanced': a.balanced,
    'kernel': a.kernel,
    'certificate_tree': a.certificate_tree,
    'compact': a.compact,
    'validation': 'Lean validation required; generated data alone is not a proof'}, indent=2), encoding='utf-8')
print(f'Generated {len(blocks)} exact blocks, 1001..{a.limit}, {a.output.stat().st_size} bytes.')
