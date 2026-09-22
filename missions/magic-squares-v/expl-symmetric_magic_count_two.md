## The order-two symmetric count: $S_{2}=M_{2}$

For order two the transpose condition is the single equation $M_{01}=M_{10}$. Every semi-magic
square already satisfies it: the first row and the first column read $M_{00}+M_{01}=t$ and
$M_{00}+M_{10}=t$, so $M_{01}=M_{10}$. Symmetry therefore adds no condition at order two and the
filtered finsets `symmetricMagicSquares 2 t` and `magicSquares 2 t` coincide, giving
$S_{2}(t)=M_{2}(t)=1$ for even $t$ and $0$ otherwise.

**Context.** Symmetry only starts to bite at order three, where it identifies three pairs of
entries and cuts MacMahon's two-parameter family down to the one-parameter family
$\mathrm{symmMagic3}(e,a)$, $0\le a\le 2e$: there $S_{3}(3e)=2e+1$ against $M_{3}(3e)=2e^{2}+2e+1$.

### Formalization notes

* The two `Finset`s are shown equal by extensionality; the forward direction is a projection and
  the backward direction adds the symmetry proof, whose only non-trivial case is $(0,1)$.
* The order-two magic count is inlined as a private helper (`private theorem magic_count_two`) so
  that the submission file is self-contained and does not depend on the publication order of the
  neighbouring node.
