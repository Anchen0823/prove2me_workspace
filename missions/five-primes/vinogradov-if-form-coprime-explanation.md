This submission proves the interval form of the source's Lemma 3.4 (with the
coprimality hypothesis $\gcd(|a'|,q)=1$ restored) from the corresponding
**block** estimate. Both children are stated with the same convention at the
zeros of the sine, so the reduction is a single application.

## Statement

Let $q\ge1$, $A'\ge0$, $B\ge0$, let $a'$ be coprime to $q$, and let
$\alpha'=\frac{a'}q+\beta'$ with $|\beta'|\le q^{-2}$. Then for all real
$\theta'$ and all $u<v$,

$$\sum_{\lfloor u\rfloor<n\le\lfloor v\rfloor}\ \mathrm{vmin}\Bigl(A',\frac B{|\sin(\pi\alpha'n+\theta')|}\Bigr)\ \le\ \Bigl(\Bigl\lfloor\frac{v-u}{q}\Bigr\rfloor+1\Bigr)\Bigl(2A'+\frac2\pi Bq\log 4q\Bigr),$$

where $\mathrm{vmin}(A',t)$ is $A'$ when the sine vanishes and $\min(A',t)$
otherwise.

## The two children

**`TaoFivePrimes.vinogradov_block_coprime`** is the estimate on a single block
of $q$ consecutive integers:

$$\sum_{m<n\le m+q}\ \mathrm{vmin}\Bigl(A',\frac B{|\sin(\pi\alpha'n+\theta')|}\Bigr)\ \le\ 2A'+\frac2\pi Bq\log 4q ,$$

for every integer $m$. This is the analytic content of the source's Lemma 3.4;
Tao's proof of that lemma reduces the general interval to it by subdivision and
then quotes the classical estimate. It is the only child that is not yet proved,
and it is exactly the statement that the platform's earlier formulation
(`vinogradov_block_if_form`) got wrong by omitting $\gcd(|a'|,q)=1$.

**`TaoFivePrimes.vinogradov_lemma_if_form_from_block`** is the subdivision
half, already **Proved** on the platform: it takes a hypothesis
`hblock : ∀ m : ℤ, ...` of exactly the shape above and returns the interval
bound with the covering count $\lfloor\frac{v-u}q\rfloor+1$, which is the
number of consecutive blocks of length $q$ needed to cover
$(\lfloor u\rfloor,\lfloor v\rfloor]$.

## Why the reduction is valid

The interval form and the block form share the parameters
$(B,q,A',\alpha',\theta')$, and the block form is quantified over *all* integer
left endpoints $m$. So the hypothesis `hblock` demanded by the subdivision
lemma is obtained by instantiating the block estimate at an arbitrary $m$ and
supplying the fixed data $(A',\alpha',\beta',\theta',a')$ together with the
coprimality, approximation and error hypotheses. The rational approximation to
$\alpha'$ plays no role in the subdivision step — it is used only inside the
block estimate — which is why the subdivision lemma does not carry it; here it
is passed straight through to the block estimate, where it belongs.

In Lean the reduction is therefore one application:

```lean
exact TaoFivePrimes.vinogradov_lemma_if_form_from_block B hB q hq A' alpha' theta' u v hA' huv
  (fun m => TaoFivePrimes.vinogradov_block_coprime B hB q hq A' alpha' beta' theta' a' hA'
    ha'q halpha' hbeta' m)
```

## Relation to the earlier, false formulation

The platform's `TaoFivePrimes.vinogradov_lemma_if_form` is the same displayed
inequality **without** $\gcd(|a'|,q)=1$, and it is false: with
$B=0$, $q=10$, $A'=1$, $a'=0$, $\alpha'=\beta'=\theta'=0$, $u=0$, $v=10$ every
one of the ten summands equals $A'=1$ while the right-hand side is
$(\lfloor 1\rfloor+1)\cdot 2 = 4$. That disproof is recorded on the node. The
present statement is the same inequality with the missing hypothesis added, and
the block estimate it reduces to is likewise the corrected version.
