import json
from pathlib import Path

root = Path(__file__).resolve().parents[3]
out = Path(__file__).resolve().parent
env = '0df444a360eaa60ab8c11dca51a86af692955474'
source = ('Jonathan Sondow, Criteria for Irrationality of Euler\'s Constant, '
          'https://arxiv.org/pdf/math/0209070 (v2, 4 October 2002). ')
def save(name, data):
    (out / name).write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding='utf-8')

save('definition-payload.json', dict(
    definition_name='eulerMascheroni_sondow',
    definition_title='Sondow harmonic sums, logarithmic forms and double integrals',
    definition=(root/'Definitions/Def_eulerMascheroni_sondow.lean').read_text(encoding='utf-8'),
    natural_language_statement=r'''Let $d_n=\operatorname{lcm}(1,\ldots,n)$ and $H_m=\sum_{j=1}^m1/j$. Define
$$A_n=\sum_{i=0}^n\binom ni^2H_{n+i},$$
$$L_n=\sum_{k=1}^n\sum_{i=0}^{\min(k-1,n-k)}\sum_{j=i+1}^{n-i}\frac{2\binom ni^2}{j}\log(n+k),$$
$$I_n=\int_0^1\int_0^1\frac{[x(1-x)y(1-y)]^n}{(1-xy)(-\log(xy))}\,dy\,dx.$$
These are Sondow's explicit quantities. His identity $d_{2n}L_n=\log S_n$ allows the criterion to use $d_{2n}L_n$ directly, without constructing the large integer product $S_n$. Results using the integral require $n>0$.''',
    source=source+'Equations (2), (6), (8), pp. 2, 3, 6; Lemma 2, p. 9.',
    env=env, tags=['euler-mascheroni','sondow','irrationality']
))

items = [
('integral_identity', 'Sondow integral evaluation',
 r'''For every positive integer $n$,
$$I_n=\binom{2n}{n}\gamma+L_n-A_n.$$
This is a known analytic identity, left as a formalization obligation.''',
 'Theorem 1, equation (7), pp. 6-9.'),
('scaled_integral_bounds','Sondow scaled positive remainder bound',
 r'''For every positive integer $n$,
$$0<d_{2n}I_n<2^{-n}.$$
This follows from the established bounds $d_{2n}<8^n$ and $0<I_n<16^{-n}$. It is a known estimate awaiting formalization.''',
 'Lemma 3, p. 10.'),
('scaled_A_integral','Clearing the denominators of Sondow harmonic sums',
 r'''For every nonnegative integer $n$,
$$d_{2n}A_n\in\mathbb Z.$$
The endpoint $n=0$ gives zero. This arithmetic fact clears the harmonic denominators in the integral identity.''',
 'Theorem 1, p. 6; denominator observation following equation (11), p. 8.'),
('fractional_lower_bound_conjecture','Open Sondow fractional-part condition for Euler irrationality',
 r'''Conjectural arithmetic condition: for every natural number $N$, there is an integer $n\ge\max(N,1)$ such that
$$\{d_{2n}L_n\}\ge2^{-n}.$$
Here $\{x\}=x-\lfloor x\rfloor$. This is the sufficient hypothesis of Sondow's Corollary 6, not a theorem proved in that paper. It is the unresolved arithmetic ingredient of this proposed route to irrationality; finite numerical evidence does not establish it.''',
 'Corollary 6, p. 11; numerical discussion p. 4. Only the conditional implication is established by the source; the displayed infinite-occurrence assertion is an open conjectural target.')
]
problems=[]
for name,title,prose,ref in items:
    full='EulerMascheroni.Sondow.'+name
    text=(root/('Theorems/Thm_'+full.replace('.','_')+'.lean')).read_text(encoding='utf-8')
    pre,statement=text.split('theorem ',1)
    problems.append(dict(theorem_name=full,theorem_title=title,
        preamble=pre.strip(),formal_statement='theorem '+statement.strip(),
        natural_language_statement=prose,source=source+ref,
        tags=['sondow','euler-mascheroni','conjecture' if 'conjecture' in name else 'formalization']))
save('problems-payload.json',dict(env=env,problems=problems))
