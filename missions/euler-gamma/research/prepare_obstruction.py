from pathlib import Path
import re, json, hashlib

root=Path(__file__).resolve().parents[3]
folder=Path(__file__).resolve().parent
src=(root/'Solutions/Sol_EulerGamma_variable_order_obstruction.lean').read_text(encoding='utf-8')
signature=re.search(r'theorem solution (.*?) := by', src, re.S).group(1)
name='EulerGammaResearch.variable_order_upper_bound'
imports='\n'.join(line for line in src.splitlines() if line.startswith('import '))+'\nopen scoped BigOperators\n'
statement='theorem '+name+' '+signature+' := by sorry'
explanation=(folder/'variable-order-explanation.md').read_text(encoding='utf-8')
payload=dict(env='0df444a360eaa60ab8c11dca51a86af692955474',problems=[dict(
    theorem_name=name,theorem_title='A uniform upper bound excluding excessive order in Euler approximants',
    formal_statement=statement,preamble=imports,natural_language_statement=explanation,
    source='Derived in the 2026-09-14 research session from the explicit finite sums. Family: Van Assche--Wolfs, https://arxiv.org/html/2404.09799v3, Section 5, displayed denominator formula and differential-operator iteration. The elementary upper bound is a session derivation, not attributed to a theorem in the paper; no claim of priority.',
    tags=['euler-mascheroni','rational-approximation','harmonic-numbers'])])
(folder/'obstruction-payload.json').write_text(json.dumps(payload,ensure_ascii=False,indent=2),encoding='utf-8')
(folder/'obstruction-statement.lean').write_text(imports+statement+'\n',encoding='utf-8')
print('Prepared payload; solution SHA256:',hashlib.sha256(src.encode()).hexdigest())
