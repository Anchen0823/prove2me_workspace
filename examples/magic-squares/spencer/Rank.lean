/-
# Brick 9: the sharp degree bound — rung S3, via the zero-line-sum space

Spencer's recursion (`Recursion.lean`) bounds the degree of the level counts by `#B`, which
aggregated gives degree `≤ n²` — one full order too high.  The sharp bound `(n-1)²` is usually
read off the face rank `ρ(B) = |B| - v(B) + c(B)` of the Birkhoff polytope, which needs the
connectivity of the support graph.  This file avoids graph theory altogether, by measuring the
rank of a support `B` as the dimension of the *zero-line-sum space*

  `zeroLineSubmodule B = {M : Fin n → Fin n → ℚ | every line sum of M is 0, supp M ⊆ B}`,

whose dimension is exactly `|B| - v(B) + c(B)` (the constraint rank `v(B) - c(B)` is never
computed, so neither are the vertices or the components).  What is needed instead:

* `rankB_univ` — `dim zeroLineSubmodule(univ) = (n-1)²`, by rank–nullity on the line-sum map
  (its range is the `Σrow = Σcol` hyperplane, of dimension `2n - 1`; surjectivity is the
  explicit transportation matrix `M i j = (a (inl i) + a (inr j) - d / n) / n`);
* the **escape lemma** — if `φ(σ) ⊆ B`, `B \ φ(σ) ⊆ C ⊆ B` and `e ∈ B \ C`, then some
  zero-line-sum matrix on `B` is nonzero at `e`.  Proof by duality: were `e` forced to zero,
  the evaluation functional at `e` would factor through the line-sum map
  (`LinearMap.range_dualMap_eq_dualAnnihilator_ker`), yielding coefficients `u` (rows) and
  `v` (columns) with `u i + v j = [ij = e]` on `B`.  Summing over the `τ`-cells `(i, τ i) ∈ C`
  gives `Σu + Σv = 0`, while summing over the `σ`-cells `(i, σ i) ∈ B` — exactly one of which
  is `e`, since `e ∈ B \ C ⊆ φ(σ)` — gives `Σu + Σv = 1`.  Contradiction;
* `rankB_lt_of_candidate` — consequently `rankB C < rankB B` for every candidate `C ⊂ B`
  that contains a permutation support (a proper subspace of equal dimension is impossible).

The payoff (rung S3b, later in this file) is `isPolyDegLe_gB_sharp` (degree `≤ rankB B` at
every support) and `exists_polynomial_semiMagicCount_sharp` (degree `≤ (n-1)²`, still for
`t ≥ 1`; the value at `t = 0` is rung S5 and is *not* claimed).  Both are **new** declarations —
the published `isPolyDegLe_gB` / `exists_polynomial_semiMagicCount_pos` are left untouched.

Scratch file, built with `lake build examples.«magic-squares».spencer.Rank`.
-/
import Mathlib
import Definitions.Def_MagicSquares
import examples.«magic-squares».spencer.Aggregate

set_option autoImplicit false
set_option maxHeartbeats 800000

open Finset

namespace MagicSquaresSpencer

open Polynomial
open MagicSquares

variable {n : ℕ}

/-! ## The line-sum functional on `ℚ`-valued matrices -/

/-- The line sums of a `ℚ`-valued matrix, as one function on `Fin n ⊕ Fin n`. -/
def lsumQ (M : Fin n → Fin n → ℚ) (a : Fin n ⊕ Fin n) : ℚ :=
  Sum.elim (fun i => ∑ j, M i j) (fun j => ∑ i, M i j) a

@[simp] theorem lsumQ_inl (M : Fin n → Fin n → ℚ) (i : Fin n) :
    lsumQ M (Sum.inl i) = ∑ j, M i j := rfl

@[simp] theorem lsumQ_inr (M : Fin n → Fin n → ℚ) (j : Fin n) :
    lsumQ M (Sum.inr j) = ∑ i, M i j := rfl

@[simp] theorem lsumQ_zero (M : Fin n → Fin n → ℚ) (a : Fin n ⊕ Fin n) : lsumQ 0 a = 0 := by
  cases a <;> simp

@[simp] theorem lsumQ_add (M N : Fin n → Fin n → ℚ) (a : Fin n ⊕ Fin n) :
    lsumQ (M + N) a = lsumQ M a + lsumQ N a := by
  cases a <;> simp [Pi.add_apply, Finset.sum_add_distrib]

@[simp] theorem lsumQ_smul (c : ℚ) (M : Fin n → Fin n → ℚ) (a : Fin n ⊕ Fin n) :
    lsumQ (c • M) a = c * lsumQ M a := by
  cases a <;> simp [Pi.smul_apply, Finset.mul_sum, smul_eq_mul]

@[simp] theorem lsumQ_sub (M N : Fin n → Fin n → ℚ) (a : Fin n ⊕ Fin n) :
    lsumQ (M - N) a = lsumQ M a - lsumQ N a := by
  cases a <;> simp [Pi.sub_apply, Finset.sum_sub_distrib]

/-- Line sums of a `ℚ`-coerced `ℕ`-matrix are the coercion of its line sum. -/
theorem lsumQ_cast {M : Matrix (Fin n) (Fin n) ℕ} {s : ℕ} (h : LineSums M s)
    (a : Fin n ⊕ Fin n) : lsumQ (fun i j => (M i j : ℚ)) a = (s : ℚ) := by
  cases a with
  | inl i => rw [lsumQ_inl, ← Nat.cast_sum, h.1 i]
  | inr j => rw [lsumQ_inr, ← Nat.cast_sum, h.2 j]

/-- The line-sum map `M ↦ (row sums, col sums)`, linear. -/
noncomputable def lineSumMap (n : ℕ) : (Fin n → Fin n → ℚ) →ₗ[ℚ] (Fin n ⊕ Fin n → ℚ) where
  toFun := lsumQ
  map_add' := by
    intro x y
    funext a
    simp [lsumQ_add, Pi.add_apply]
  map_smul' := by
    intro m x
    funext a
    simp [lsumQ_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

/-- The imbalance functional `a ↦ Σrow a - Σcol a`, linear. -/
noncomputable def imbalanceMap (n : ℕ) : (Fin n ⊕ Fin n → ℚ) →ₗ[ℚ] ℚ where
  toFun a := ∑ i, a (Sum.inl i) - ∑ j, a (Sum.inr j)
  map_add' := by
    intro x y
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' := by
    intro m x
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.mul_sum, mul_sub]

/-- The `Σrow = Σcol` hyperplane. -/
noncomputable def balanceSpace (n : ℕ) : Submodule ℚ (Fin n ⊕ Fin n → ℚ) where
  carrier := {a | ∑ i, a (Sum.inl i) = ∑ j, a (Sum.inr j)}
  add_mem' := by
    intro a b ha hb
    rw [Set.mem_setOf_eq] at ha hb ⊢
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    rw [ha, hb]
  zero_mem' := by rw [Set.mem_setOf_eq]; simp
  smul_mem' := by
    intro c a ha
    rw [Set.mem_setOf_eq] at ha ⊢
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ha]

theorem mem_balanceSpace (a : Fin n ⊕ Fin n → ℚ) :
    a ∈ balanceSpace n ↔ ∑ i, a (Sum.inl i) = ∑ j, a (Sum.inr j) := Iff.rfl

theorem mem_balanceSpace_iff (x : Fin n ⊕ Fin n → ℚ) :
    x ∈ balanceSpace n ↔ imbalanceMap n x = 0 := by
  constructor
  · intro h
    have hx : ∑ i, x (Sum.inl i) = ∑ j, x (Sum.inr j) := (mem_balanceSpace x).mp h
    show ∑ i, x (Sum.inl i) - ∑ j, x (Sum.inr j) = 0
    rw [hx]
    ring
  · intro h
    have hx : ∑ i, x (Sum.inl i) - ∑ j, x (Sum.inr j) = 0 := h
    exact (mem_balanceSpace x).mpr (by linarith)

theorem range_lineSumMap_le_balance (n : ℕ) :
    LinearMap.range (lineSumMap n) ≤ balanceSpace n := by
  intro a ha
  obtain ⟨M, rfl⟩ := ha
  have heq : ∑ i, lsumQ M (Sum.inl i) = ∑ j, lsumQ M (Sum.inr j) := by
    simp only [lsumQ_inl, lsumQ_inr]
    rw [Finset.sum_comm]
  exact heq

/-- **Surjectivity onto the balance hyperplane**, by the explicit transportation matrix
`M i j = (a (inl i) + a (inr j) - d / n) / n` with `d = Σcol a`. -/
theorem balance_le_range_lineSumMap {n : ℕ} (hn : 1 ≤ n) :
    balanceSpace n ≤ LinearMap.range (lineSumMap n) := by
  intro a ha
  have hd : ∑ i, a (Sum.inl i) = ∑ k, a (Sum.inr k) := (mem_balanceSpace a).mp ha
  have hne : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsumconst : ∀ x : ℚ, (∑ _j : Fin n, x) = n * x := by intro x; simp
  have hq : ∀ z : ℚ, (n : ℚ) * (z / (n : ℚ)) = z := fun z => by
    rw [mul_comm, div_mul_cancel₀ _ hne]
  have hrow : ∀ i : Fin n,
      (∑ j : Fin n, ((a (Sum.inl i) + a (Sum.inr j)
        - (∑ k : Fin n, a (Sum.inr k)) / (n : ℚ)) / (n : ℚ))) = a (Sum.inl i) := by
    intro i
    have key : ∀ j : Fin n,
        ((a (Sum.inl i) + a (Sum.inr j) - (∑ k : Fin n, a (Sum.inr k)) / (n : ℚ)) / (n : ℚ))
          = ((a (Sum.inl i) - (∑ k : Fin n, a (Sum.inr k)) / (n : ℚ)) / (n : ℚ)
              + a (Sum.inr j) / (n : ℚ)) := fun _ => by ring
    rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_add_distrib, hsumconst,
      ← Finset.sum_div, mul_div_cancel₀ _ hne, sub_add_cancel]
  have hcol : ∀ j : Fin n,
      (∑ i : Fin n, ((a (Sum.inl i) + a (Sum.inr j)
        - (∑ k : Fin n, a (Sum.inr k)) / (n : ℚ)) / (n : ℚ))) = a (Sum.inr j) := by
    intro j
    have key : ∀ i : Fin n,
        ((a (Sum.inl i) + a (Sum.inr j) - (∑ k : Fin n, a (Sum.inr k)) / (n : ℚ)) / (n : ℚ))
          = ((a (Sum.inr j) - (∑ k : Fin n, a (Sum.inr k)) / (n : ℚ)) / (n : ℚ)
              + a (Sum.inl i) / (n : ℚ)) := fun _ => by ring
    rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib, hsumconst,
      ← Finset.sum_div, hd, mul_div_cancel₀ _ hne, sub_add_cancel]
  refine LinearMap.mem_range.mpr
    ⟨fun i j => (a (Sum.inl i) + a (Sum.inr j)
      - (∑ k : Fin n, a (Sum.inr k)) / (n : ℚ)) / (n : ℚ), ?_⟩
  funext a'
  cases a' with
  | inl i => exact hrow i
  | inr j => exact hcol j

theorem range_lineSumMap_eq_balance {n : ℕ} (hn : 1 ≤ n) :
    LinearMap.range (lineSumMap n) = balanceSpace n :=
  le_antisymm (range_lineSumMap_le_balance n) (balance_le_range_lineSumMap hn)

/-! ## The zero-line-sum space, the equal-line-sum space, and the rank -/

/-- `M` has zero line sums and is supported inside `B`. -/
def IsZeroLine (B : Finset (Fin n × Fin n)) (M : Fin n → Fin n → ℚ) : Prop :=
  (∀ a, lsumQ M a = 0) ∧ ∀ i j, (i, j) ∉ B → M i j = 0

/-- `M` has all line sums equal to each other and is supported inside `B`. -/
def IsEqLine (B : Finset (Fin n × Fin n)) (M : Fin n → Fin n → ℚ) : Prop :=
  (∀ a b, lsumQ M a = lsumQ M b) ∧ ∀ i j, (i, j) ∉ B → M i j = 0

theorem IsZeroLine.eqLine {B : Finset (Fin n × Fin n)} {M : Fin n → Fin n → ℚ}
    (h : IsZeroLine B M) : IsEqLine B M :=
  ⟨fun a b => (h.1 a).trans (h.1 b).symm, h.2⟩

/-- The zero-line-sum space of a support. -/
def zeroLineSubmodule (B : Finset (Fin n × Fin n)) : Submodule ℚ (Fin n → Fin n → ℚ) where
  carrier := {M | IsZeroLine B M}
  add_mem' := by
    intro a b ha hb
    refine ⟨fun c => by rw [lsumQ_add, ha.1 c, hb.1 c, add_zero], fun i j hij => ?_⟩
    simp only [Pi.add_apply]
    rw [ha.2 i j hij, hb.2 i j hij, add_zero]
  zero_mem' := ⟨fun a => lsumQ_zero 0 a, fun _ _ _ => rfl⟩
  smul_mem' := by
    intro c a ha
    refine ⟨fun b => by rw [lsumQ_smul, ha.1 b, mul_zero], fun i j hij => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [ha.2 i j hij, mul_zero]

/-- The equal-line-sum space of a support. -/
def eqLineSubmodule (B : Finset (Fin n × Fin n)) : Submodule ℚ (Fin n → Fin n → ℚ) where
  carrier := {M | IsEqLine B M}
  add_mem' := by
    intro a b ha hb
    refine ⟨fun c d => by rw [lsumQ_add, lsumQ_add, ha.1 c d, hb.1 c d], fun i j hij => ?_⟩
    simp only [Pi.add_apply]
    rw [ha.2 i j hij, hb.2 i j hij, add_zero]
  zero_mem' := ⟨fun a b => (lsumQ_zero 0 a).trans (lsumQ_zero 0 b).symm, fun _ _ _ => rfl⟩
  smul_mem' := by
    intro c a ha
    refine ⟨fun d e => by rw [lsumQ_smul, lsumQ_smul, ha.1 d e], fun i j hij => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [ha.2 i j hij, mul_zero]

/-- **The rank of a support**: the dimension of its zero-line-sum space.  This is the face
rank `ρ(B) = |B| - v(B) + c(B)` in disguise; the graph never appears. -/
noncomputable def rankB (B : Finset (Fin n × Fin n)) : ℕ :=
  Module.finrank ℚ (zeroLineSubmodule B)

theorem mem_zeroLineSubmodule {B : Finset (Fin n × Fin n)} {M : Fin n → Fin n → ℚ} :
    M ∈ zeroLineSubmodule B ↔ IsZeroLine B M := ⟨fun h => h, fun h => h⟩

theorem mem_eqLineSubmodule {B : Finset (Fin n × Fin n)} {M : Fin n → Fin n → ℚ} :
    M ∈ eqLineSubmodule B ↔ IsEqLine B M := ⟨fun h => h, fun h => h⟩
theorem ker_lineSumMap (n : ℕ) :
    LinearMap.ker (lineSumMap n) = zeroLineSubmodule (Finset.univ : Finset (Fin n × Fin n)) := by
  ext M
  constructor
  · intro h
    rw [mem_zeroLineSubmodule]
    refine ⟨fun a => congrFun h a, fun i j hij => absurd (Finset.mem_univ (i, j)) hij⟩
  · intro h
    rw [LinearMap.mem_ker]
    funext a
    show lsumQ M a = 0
    exact (mem_zeroLineSubmodule.mp h).1 a

/-! ### two finrank helpers -/

theorem finrank_le_finrank_of_le {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] {p q : Submodule ℚ V} (h : p ≤ q) :
    Module.finrank ℚ ↥p ≤ Module.finrank ℚ ↥q := by
  have hinj : Function.Injective (Submodule.inclusion h) := Submodule.inclusion_injective h
  have hr : Module.finrank ℚ (LinearMap.range (Submodule.inclusion h))
      = Module.finrank ℚ ↥p := LinearMap.finrank_range_of_inj hinj
  calc Module.finrank ℚ ↥p
      = Module.finrank ℚ (LinearMap.range (Submodule.inclusion h)) := hr.symm
    _ ≤ Module.finrank ℚ ↥q := Submodule.finrank_le _

theorem finrank_lt_of_proper_le {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] {p q : Submodule ℚ V} (hpq : p ≤ q) (hne : p ≠ q) :
    Module.finrank ℚ ↥p < Module.finrank ℚ ↥q := by
  have hinj : Function.Injective (Submodule.inclusion hpq) := Submodule.inclusion_injective hpq
  have hr : Module.finrank ℚ (LinearMap.range (Submodule.inclusion hpq))
      = Module.finrank ℚ ↥p := LinearMap.finrank_range_of_inj hinj
  have hne2 : LinearMap.range (Submodule.inclusion hpq) ≠ ⊤ := by
    intro heq
    have hnotle : ¬ (q ≤ p) := fun h => hne (le_antisymm hpq h)
    obtain ⟨x, hxq, hxp⟩ : ∃ x : V, x ∈ q ∧ x ∉ p := by
      by_contra hall
      push_neg at hall
      exact hnotle fun y hy => hall y hy
    have hxq' : (⟨x, hxq⟩ : ↥q) ∈ LinearMap.range (Submodule.inclusion hpq) := by
      rw [heq]; exact Submodule.mem_top
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hxq'
    have hy2 : (y : V) = x := congrArg Subtype.val hy
    refine hxp ?_
    rw [← hy2]
    exact y.2
  calc Module.finrank ℚ ↥p
      = Module.finrank ℚ (LinearMap.range (Submodule.inclusion hpq)) := hr.symm
    _ < Module.finrank ℚ ↥q := Submodule.finrank_lt hne2

/-! ### rank monotonicity -/

theorem zeroLineSubmodule_mono {B C : Finset (Fin n × Fin n)} (h : B ⊆ C) :
    zeroLineSubmodule B ≤ zeroLineSubmodule C := by
  intro M hM
  exact ⟨hM.1, fun i j hij => hM.2 i j fun hc => hij (h hc)⟩

theorem rankB_mono {B C : Finset (Fin n × Fin n)} (h : B ⊆ C) : rankB B ≤ rankB C :=
  finrank_le_finrank_of_le (zeroLineSubmodule_mono h)

/-- **The rank of the full support is `(n-1)²`.**  Rank–nullity on the line-sum map: the domain
has dimension `n²`, the range is the `(2n-1)`-dimensional `Σrow = Σcol` hyperplane. -/
theorem rankB_univ (n : ℕ) :
    rankB (Finset.univ : Finset (Fin n × Fin n)) = (n - 1) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn1
  · subst hn0
    have hV : Module.finrank ℚ (Fin 0 → Fin 0 → ℚ) = 0 := by
      rw [Module.finrank_pi_fintype]; simp
    have hle := Submodule.finrank_le (zeroLineSubmodule (Finset.univ : Finset (Fin 0 × Fin 0)))
    simp only [rankB] at hle ⊢
    have hz : ((0 : ℕ) - 1) ^ 2 = 0 := by norm_num
    omega
  · -- finrank of the domain
    have hV : Module.finrank ℚ (Fin n → Fin n → ℚ) = n * n := by
      rw [Module.finrank_pi_fintype]
      have hint : ∀ _i : Fin n, Module.finrank ℚ (Fin n → ℚ) = n := fun _ => by
        rw [Module.finrank_pi]; simp
      simp [hint]
    -- finrank of the range: the balance hyperplane, dimension 2n - 1
    have hfr := LinearMap.finrank_range_add_finrank_ker (f := lineSumMap n)
    rw [range_lineSumMap_eq_balance hn1, hV] at hfr
    have hbal : Module.finrank ℚ (balanceSpace n) = 2 * n - 1 := by
      -- the balance hyperplane is a codimension-one subspace: ⊤ = balance ⊔ ℚ∙δ
      set δ : Fin n ⊕ Fin n → ℚ :=
        Sum.elim (fun i : Fin n => if i.val = 0 then (1 : ℚ) else 0) (fun _ => (0 : ℚ))
        with hδdef
      have hδrow : ∑ i : Fin n, δ (Sum.inl i) = 1 := by
        rw [Finset.sum_eq_single (⟨0, hn1⟩ : Fin n)]
        · simp [hδdef]
        · intro b _ hb
          simp only [hδdef, Sum.elim_inl]
          rw [if_neg (fun h : b.val = 0 => hb (Fin.ext h))]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hδf : imbalanceMap n δ = 1 := by
        show ∑ i : Fin n, δ (Sum.inl i) - ∑ j : Fin n, δ (Sum.inr j) = 1
        rw [hδrow]
        have hδcol : ∑ j : Fin n, δ (Sum.inr j) = 0 := by
          simp [hδdef]
        rw [hδcol]
        norm_num
      have hδne : δ ≠ 0 := by
        intro h
        have h0 : δ (Sum.inl (⟨0, hn1⟩ : Fin n)) = 0 := congrFun h _
        simp [hδdef] at h0
      have hsup : balanceSpace n ⊔ Submodule.span ℚ {δ} = ⊤ := by
        refine le_antisymm le_top ?_
        intro a ha
        refine Submodule.mem_sup.mpr ⟨a - imbalanceMap n a • δ, ?_, imbalanceMap n a • δ, ?_, ?_⟩
        · have hc : imbalanceMap n (a - imbalanceMap n a • δ) = 0 := by
            rw [map_sub, map_smul, hδf, smul_eq_mul, mul_one, sub_self]
          exact (mem_balanceSpace_iff _).mpr hc
        · exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self δ)
        · exact sub_add_cancel _ _
      have hinf : balanceSpace n ⊓ Submodule.span ℚ {δ} = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro x hx
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx.2
        have himm : imbalanceMap n x = 0 := by
          have hxeq : ∑ i : Fin n, x (Sum.inl i) = ∑ j : Fin n, x (Sum.inr j) :=
            (mem_balanceSpace x).mp hx.1
          show ∑ i : Fin n, x (Sum.inl i) - ∑ j : Fin n, x (Sum.inr j) = 0
          rw [hxeq]
          ring
        rw [← hc] at himm
        rw [map_smul, hδf, smul_eq_mul, mul_one] at himm
        rw [← hc, himm, zero_smul]
      have hcard := Submodule.finrank_sup_add_finrank_inf_eq (balanceSpace n)
        (Submodule.span ℚ {δ})
      rw [hsup, hinf, finrank_top ℚ (Fin n ⊕ Fin n → ℚ), finrank_bot ℚ (Fin n ⊕ Fin n → ℚ),
        finrank_span_singleton hδne] at hcard
      have hV2 : Module.finrank ℚ (Fin n ⊕ Fin n → ℚ) = 2 * n := by
        rw [Module.finrank_pi, Fintype.card_sum, Fintype.card_fin]
        ring
      rw [hV2] at hcard
      omega
    rw [hbal] at hfr
    rw [ker_lineSumMap] at hfr
    simp only [rankB]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hnm : m + 1 - 1 = m := by omega
    rw [hnm]
    have e1 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    rw [e1] at hfr
    have key : 2 * m + 1 + m ^ 2 = (m + 1) * (m + 1) := by ring
    omega

/-! ## The escape lemma: cells outside a permutation-containing candidate are not forced

This is the strictness input for rung S3b.  If `φ(σ) ⊆ B`, `B \ φ(σ) ⊆ C ⊆ B` (the shape every
candidate of the support recursion has) and `e ∈ B \ C`, then some zero-line-sum matrix on `B`
is nonzero at `e`; hence `rankB C < rankB B` for every candidate that contains a permutation. -/

/-- The free space on a support: all matrices supported inside `B`, no line-sum condition. -/
def suppSubmodule (B : Finset (Fin n × Fin n)) : Submodule ℚ (Fin n → Fin n → ℚ) where
  carrier := {M | ∀ i j, (i, j) ∉ B → M i j = 0}
  add_mem' := by
    intro a b ha hb i j hij
    have ha' : a i j = 0 := ha i j hij
    have hb' : b i j = 0 := hb i j hij
    show a i j + b i j = 0
    rw [ha', hb']
    norm_num
  zero_mem' := fun _ _ _ => rfl
  smul_mem' := by
    intro c a ha i j hij
    have ha' : a i j = 0 := ha i j hij
    show c * a i j = 0
    rw [ha', mul_zero]

theorem mem_suppSubmodule {B : Finset (Fin n × Fin n)} {M : Fin n → Fin n → ℚ} :
    M ∈ suppSubmodule B ↔ ∀ i j, (i, j) ∉ B → M i j = 0 := ⟨fun h => h, fun h => h⟩

/-- The evaluation functional at a cell. -/
noncomputable def evalCell (e : Fin n × Fin n) : (Fin n → Fin n → ℚ) →ₗ[ℚ] ℚ where
  toFun M := M e.1 e.2
  map_add' x y := by simp
  map_smul' c x := by simp

/-- The line-sum map restricted to the free space of `B`. -/
noncomputable def lineSumMapOn (B : Finset (Fin n × Fin n)) :
    ↥(suppSubmodule B) →ₗ[ℚ] (Fin n ⊕ Fin n → ℚ) :=
  (lineSumMap n).comp (suppSubmodule B).subtype

/-- The evaluation functional at a cell, restricted to the free space of `B`. -/
noncomputable def evalCellOn (B : Finset (Fin n × Fin n)) (e : Fin n × Fin n) :
    ↥(suppSubmodule B) →ₗ[ℚ] ℚ :=
  (evalCell e).comp (suppSubmodule B).subtype

/-- The unit matrix at a cell. -/
def unitMat (f : Fin n × Fin n) : Fin n → Fin n → ℚ :=
  fun p q => if (p, q) = f then (1 : ℚ) else 0

theorem unitMat_mem_supp (f : Fin n × Fin n) (B : Finset (Fin n × Fin n)) (hf : f ∈ B) :
    unitMat f ∈ suppSubmodule B := by
  intro p q hpq
  show (if (p, q) = f then (1 : ℚ) else 0) = 0
  by_cases hc : (p, q) = f
  · exact absurd (by rw [hc]; exact hf) hpq
  · rw [if_neg hc]

theorem unitMat_row (i j k : Fin n) :
    ∑ l, unitMat (i, j) k l = if k = i then (1 : ℚ) else 0 := by
  by_cases h : k = i
  · rw [h]
    have hR : (if i = i then (1 : ℚ) else 0) = 1 := if_pos rfl
    rw [hR]
    refine Eq.trans (Finset.sum_eq_single j (fun b _ hb => ?_) (fun hcon => ?_)) ?_
    · show (if (i, b) = (i, j) then (1 : ℚ) else 0) = 0
      rw [if_neg (fun hc => hb (congrArg Prod.snd hc))]
    · exact absurd (Finset.mem_univ j) hcon
    · show (if (i, j) = (i, j) then (1 : ℚ) else 0) = 1
      rw [if_pos rfl]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun q _ => ?_
    show (if (k, q) = (i, j) then (1 : ℚ) else 0) = 0
    rw [if_neg (fun hc => h (congrArg Prod.fst hc))]

theorem unitMat_col (i j k : Fin n) :
    ∑ l, unitMat (i, j) l k = if k = j then (1 : ℚ) else 0 := by
  by_cases h : k = j
  · rw [h]
    have hR : (if j = j then (1 : ℚ) else 0) = 1 := if_pos rfl
    rw [hR]
    refine Eq.trans (Finset.sum_eq_single i (fun b _ hb => ?_) (fun hcon => ?_)) ?_
    · show (if (b, j) = (i, j) then (1 : ℚ) else 0) = 0
      rw [if_neg (fun hc => hb (congrArg Prod.fst hc))]
    · exact absurd (Finset.mem_univ i) hcon
    · show (if (i, j) = (i, j) then (1 : ℚ) else 0) = 1
      rw [if_pos rfl]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun p _ => ?_
    show (if (p, k) = (i, j) then (1 : ℚ) else 0) = 0
    rw [if_neg (fun hc => h (congrArg Prod.snd hc))]

theorem unitMat_eval (i j : Fin n) (p : Fin n × Fin n) :
    unitMat (i, j) p.1 p.2 = if p = (i, j) then (1 : ℚ) else 0 := by
  unfold unitMat
  by_cases h : p = (i, j)
  · simp [h]
  · simp [h]

/-- **The dual certificate.**  If every zero-line-sum matrix supported on `B` vanishes at `e`,
then on `B` the indicator of `e` is of the form `u i + v j` — one coefficient per row and per
column.  This is the duality step: the evaluation functional at `e` factors through the
line-sum map (`LinearMap.range_dualMap_eq_dualAnnihilator_ker`), and a functional on the
line-sum target is a combination of row and column coordinates. -/
theorem exists_dual_of_forced {B : Finset (Fin n × Fin n)} {e : Fin n × Fin n}
    (hall : ∀ M ∈ zeroLineSubmodule B, M e.1 e.2 = 0) :
    ∃ u v : Fin n → ℚ, ∀ i j : Fin n, (i, j) ∈ B →
      u i + v j = if (i, j) = e then (1 : ℚ) else 0 := by
  classical
  have hker : LinearMap.ker (lineSumMapOn B) ≤ LinearMap.ker (evalCellOn B e) := by
    intro M hM
    simp only [LinearMap.mem_ker] at hM ⊢
    have hMl : ∀ a, lsumQ (M : Fin n → Fin n → ℚ) a = 0 := fun a => congrFun hM a
    show (M : Fin n → Fin n → ℚ) e.1 e.2 = 0
    exact hall (M : Fin n → Fin n → ℚ) ⟨hMl, mem_suppSubmodule.mp M.2⟩
  have hmem : evalCellOn B e ∈ LinearMap.range (lineSumMapOn B).dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker]
    exact (Submodule.mem_dualAnnihilator _).2 hker
  obtain ⟨g, hg⟩ := LinearMap.mem_range.mp hmem
  have hval : ∀ M : ↥(suppSubmodule B), g (lineSumMapOn B M) = evalCellOn B e M := by
    intro M
    rw [← hg, LinearMap.dualMap_apply]
  have hgsum : ∀ a : Fin n ⊕ Fin n → ℚ, g a
      = ∑ p, a (Sum.inl p) * g (Pi.single (Sum.inl p) (1 : ℚ))
        + ∑ q, a (Sum.inr q) * g (Pi.single (Sum.inr q) (1 : ℚ)) := by
    intro a
    have hdecomp : a = ∑ x : Fin n ⊕ Fin n, a x • Pi.single x (1 : ℚ) := by
      funext y
      rw [Finset.sum_apply]
      simp [Pi.smul_apply, Pi.single_apply]
    calc g a = g (∑ x : Fin n ⊕ Fin n, a x • Pi.single x (1 : ℚ)) := by
          conv_lhs => rw [hdecomp]
      _ = ∑ x : Fin n ⊕ Fin n, a x * g (Pi.single x (1 : ℚ)) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun x _ => by rw [map_smul, smul_eq_mul]
      _ = (∑ p, a (Sum.inl p) * g (Pi.single (Sum.inl p) (1 : ℚ))
            + ∑ q, a (Sum.inr q) * g (Pi.single (Sum.inr q) (1 : ℚ))) :=
            Fintype.sum_sum_type
              (fun x => a x * g (Pi.single x (1 : ℚ)))
  refine ⟨fun i => g (Pi.single (Sum.inl i) (1 : ℚ)), fun j => g (Pi.single (Sum.inr j) (1 : ℚ)),
    fun i j hij => ?_⟩
  have hδmem : unitMat (i, j) ∈ suppSubmodule B := unitMat_mem_supp (i, j) B hij
  have h1 : g (lsumQ (unitMat (i, j)))
      = ∑ p, (if p = i then (1 : ℚ) else 0) * g (Pi.single (Sum.inl p) (1 : ℚ))
        + ∑ q, (if q = j then (1 : ℚ) else 0) * g (Pi.single (Sum.inr q) (1 : ℚ)) := by
    rw [hgsum (lsumQ (unitMat (i, j)))]
    simp only [lsumQ_inl, lsumQ_inr, unitMat_row, unitMat_col]
  have hL : ∑ p, (if p = i then (1 : ℚ) else 0) * g (Pi.single (Sum.inl p) (1 : ℚ))
      = g (Pi.single (Sum.inl i) (1 : ℚ)) := by
    simp [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
  have hR : ∑ q, (if q = j then (1 : ℚ) else 0) * g (Pi.single (Sum.inr q) (1 : ℚ))
      = g (Pi.single (Sum.inr j) (1 : ℚ)) := by
    simp [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
  have hval2 := hval ⟨unitMat (i, j), hδmem⟩
  rw [show lineSumMapOn B ⟨unitMat (i, j), hδmem⟩ = lsumQ (unitMat (i, j)) from rfl, h1, hL,
    hR, show evalCellOn B e ⟨unitMat (i, j), hδmem⟩
      = if (i, j) = e then (1 : ℚ) else 0 from by
        show unitMat (i, j) e.1 e.2 = _
        rw [unitMat_eval]
        by_cases hc : (i, j) = e
        · rw [if_pos hc, if_pos (by rw [hc])]
        · rw [if_neg hc, if_neg (fun hc' => hc hc'.symm)]] at hval2
  exact hval2

/-- **The escape lemma.**  If `φ(σ) ⊆ B`, `B \ φ(σ) ⊆ C ⊆ B` (the shape of every candidate of
the support recursion), `φ(τ) ⊆ C`, and `e ∈ B \ C`, then some zero-line-sum matrix supported
on `B` is nonzero at `e`: the cell `e` is not forced to zero. -/
theorem exists_zeroLine_touching {B C : Finset (Fin n × Fin n)}
    (σ τ : Equiv.Perm (Fin n)) (hφB : matSupport (permMatrix σ) ⊆ B)
    (hφC : matSupport (permMatrix τ) ⊆ C)
    (hC : B \ matSupport (permMatrix σ) ⊆ C) (hCB : C ⊆ B)
    (e : Fin n × Fin n) (heB : e ∈ B) (heC : e ∉ C) :
    ∃ M : Fin n → Fin n → ℚ, M ∈ zeroLineSubmodule B ∧ M e.1 e.2 ≠ 0 := by
  classical
  by_contra hall
  push_neg at hall
  obtain ⟨u, v, hcert⟩ := exists_dual_of_forced hall
  -- `e` lies on `σ`'s permutation
  have heφ : e ∈ matSupport (permMatrix σ) := by
    by_contra hne
    exact heC (hC (Finset.mem_sdiff.mpr ⟨heB, hne⟩))
  rw [matSupport_permMatrix] at heφ
  obtain ⟨i₀, -, he⟩ := Finset.mem_image.mp heφ
  -- he : (i₀, σ i₀) = e
  have hi₀ : ∀ i : Fin n, ((i, σ i) = e ↔ i = i₀) := by
    intro i
    constructor
    · intro hc
      exact (congrArg Prod.fst hc).trans (congrArg Prod.fst he).symm
    · intro hc
      rw [hc]
      exact he
  -- summing the certificate over the `τ`-cells (all in `C`, none equal to `e`) gives `Σu + Σv = 0`
  have hτ0 : ∑ i : Fin n, (u i + v (τ i)) = 0 := by
    have h2 : ∀ i : Fin n, u i + v (τ i) = (0 : ℚ) := by
      intro i
      have h := hcert i (τ i) (hCB (hφC (mem_matSupport_permMatrix_self τ i)))
      rw [if_neg (fun hc => heC (by rw [← hc]; exact hφC (mem_matSupport_permMatrix_self τ i)))]
        at h
      exact h
    rw [Finset.sum_congr rfl fun i _ => h2 i]
    simp
  -- summing over the `σ`-cells (all in `B`, exactly one equal to `e`) gives `Σu + Σv = 1`
  have hσ1 : ∑ i : Fin n, (u i + v (σ i)) = 1 := by
    have h2 : ∀ i : Fin n, u i + v (σ i) = if i = i₀ then (1 : ℚ) else 0 := by
      intro i
      have h := hcert i (σ i) (hφB (mem_matSupport_permMatrix_self σ i))
      simp only [hi₀ i] at h
      exact h
    rw [Finset.sum_congr rfl fun i _ => h2 i]
    simp
  -- both sums equal `Σu + Σv`
  have hreindex : ∑ i : Fin n, (u i + v (σ i)) = ∑ i : Fin n, (u i + v (τ i)) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Equiv.sum_comp σ v, ← Equiv.sum_comp τ v]
  rw [hreindex, hτ0] at hσ1
  norm_num at hσ1

/-- **Strict monotonicity on candidates.**  If `φ(σ) ⊆ B`, `B \ φ(σ) ⊆ C ⊂ B` and `C` contains
a permutation support, then `rankB C < rankB B`. -/
theorem rankB_lt_of_candidate {B C : Finset (Fin n × Fin n)}
    (σ τ : Equiv.Perm (Fin n)) (hφB : matSupport (permMatrix σ) ⊆ B)
    (hφC : matSupport (permMatrix τ) ⊆ C)
    (hC : B \ matSupport (permMatrix σ) ⊆ C) (hCB : C ⊂ B) :
    rankB C < rankB B := by
  classical
  obtain ⟨e, heB, heC⟩ : ∃ e, e ∈ B ∧ e ∉ C := by
    by_contra hall
    push_neg at hall
    exact hCB.2 fun x hx => hall x hx
  obtain ⟨M, hM, hMne⟩ :=
    exists_zeroLine_touching σ τ hφB hφC hC hCB.1 e heB heC
  have hprop : zeroLineSubmodule C ≠ zeroLineSubmodule B := by
    intro heq
    apply hMne
    have hMC : M ∈ zeroLineSubmodule C := by rw [heq]; exact hM
    exact hMC.2 e.1 e.2 heC
  exact finrank_lt_of_proper_le (zeroLineSubmodule_mono hCB.1) hprop

theorem rankB_empty (n : ℕ) : rankB (∅ : Finset (Fin n × Fin n)) = 0 := by
  refine Submodule.finrank_eq_zero.mpr ?_
  rw [Submodule.eq_bot_iff]
  intro M hM
  refine Submodule.mem_bot ℚ |>.mpr ?_
  ext i j
  exact hM.2 i j (by simp)

end MagicSquaresSpencer
