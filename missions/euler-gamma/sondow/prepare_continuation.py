import json
from pathlib import Path
root=Path(__file__).resolve().parents[3]
out=Path(__file__).resolve().parent/'continuation'
out.mkdir(exist_ok=True)
env='0df444a360eaa60ab8c11dca51a86af692955474'
source='J. Sondow, https://arxiv.org/pdf/math/0209070, v2 (2002). '
def save(name,obj):
    (out/name).write_text(json.dumps(obj,ensure_ascii=False,indent=2),encoding='utf-8')
save('definition-payload.json',dict(
    definition_name='eulerMascheroni_sondowCutoff',
    definition_title='Sondow cutoff remainder and finite-shift correction',
    definition=(root/'Definitions/Def_eulerMascheroni_sondowCutoff.lean').read_text(encoding='utf-8'),
    natural_language_statement=r'''Write $K_n(x,y)=[x(1-x)y(1-y)]^n/((1-xy)(-\log(xy)))$. Define
$$R_{n,N}=\int_0^1\int_0^1 K_n(x,y)(xy)^N\,dy\,dx,$$
$$E_{n,N}=\sum_{i=0}^n\binom ni^2(H_{N+n+i}-H_N)
+2\sum_{0\le i<j\le n}\frac{(-1)^{i+j}\binom ni\binom nj}{j-i}
\sum_{k=1}^{j-i}\log\left(1+\frac{n+i+k}{N}\right).$$
The remainder comes from truncating the geometric series. The correction collects finite shifts after extracting $H_N-\log N$. The finite evaluation uses $n,N>0$; no theorem is asserted by these definitions.''',
    source=source+'Equation (9), p. 7; finite evaluation and asymptotic rearrangement, pp. 8-9.',env=env,
    tags=['sondow','euler-mascheroni','analysis']))
items=[
('integral_bounds','Positive exponential decay of the Sondow integrals',
 r'''For every positive integer $n$,
$$0<I_n<16^{-n}.$$
This is the integral part of Sondow's Lemma 3. It does not use a bound for the least common multiple or the integral evaluation involving Euler's constant.''',
 'Lemma 3, p. 10. An alternative elementary majorant is proved in the submitted solution.'),
('remainder_tendsto_zero','Vanishing of the Sondow geometric-series remainder',
 r'''For each fixed positive integer $n$,
$$\lim_{N\to\infty}R_{n,N}=0.$$
This justifies removing the geometric-series cutoff in the double integral.''',
 'Equation (9), p. 7, and the vanishing-remainder argument, p. 9.'),
('cutoffError_tendsto_zero','Vanishing finite-shift correction in Sondow evaluation',
 r'''For every fixed nonnegative integer $n$,
$$\lim_{N\to\infty}E_{n,N}=0.$$
This records the elementary limits of the finite harmonic and logarithmic shifts in the cutoff evaluation. The case $n=0$ is included.''',
 'Finite-shift asymptotics immediately preceding equation (11), p. 8; explicit rearrangement into the defined correction.'),
('finite_cutoff_identity','Finite cutoff evaluation for Sondow integrals',
 r'''For positive integers $n,N$,
$$I_n-R_{n,N}=\binom{2n}{n}(H_N-\log N)+L_n-A_n+E_{n,N}.$$
This finite identity combines the binomial expansion, integration of the geometric truncation, and the combinatorial identification of the logarithmic form. It is a known source-derived identity awaiting formalization; it assumes no irrationality conjecture.''',
 'Finite evaluation, p. 8, with equations (6), (8), (11), the binomial identities on p. 9, and Lemma 2. The displayed statement is an exact rearrangement for N>0.')]
problems=[]
for name,title,prose,ref in items:
    full='EulerMascheroni.Sondow.'+name
    code=(root/('Theorems/Thm_'+full.replace('.','_')+'.lean')).read_text(encoding='utf-8')
    pre,stmt=code.split('theorem ',1)
    problems.append(dict(theorem_name=full,theorem_title=title,preamble=pre.strip(),formal_statement='theorem '+stmt.strip(),
        natural_language_statement=prose,source=source+ref,tags=['sondow','formalization','analysis']))
save('problems-payload.json',dict(env=env,problems=problems))
