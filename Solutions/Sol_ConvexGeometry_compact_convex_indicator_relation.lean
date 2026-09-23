import Mathlib

set_option autoImplicit false
attribute [local instance] Classical.propDecidable


/-! From ClosedIntervalIndicator.lean -/
set_option autoImplicit false

namespace MagicSquaresEuler

open Finset

/-- A finite set has a right neighborhood of `r` containing no member strictly
between `r` and its endpoint. -/
theorem exists_right_gap (S : Finset ℝ) (r : ℝ) :
    ∃ t : ℝ, r < t ∧ ∀ s ∈ S, r < s → t < s := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨r + 1, by linarith, ?_⟩
    simp
  | @insert s S hs ih =>
    obtain ⟨t, hrt, ht⟩ := ih
    by_cases hrs : r < s
    · refine ⟨min t ((r + s) / 2), lt_min hrt (by linarith), ?_⟩
      intro u hu hru
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
      · exact lt_of_le_of_lt (min_le_left _ _) (ht u hu hru)
    · refine ⟨t, hrt, ?_⟩
      intro u hu hru
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact False.elim (hrs hru)
      · exact ht u hu hru

end MagicSquaresEuler

/-! From ClosedIntervalValuation.lean -/
set_option autoImplicit false

namespace MagicSquaresEuler

open Finset

/-- Any finite pointwise relation between indicators of nonempty compact real
intervals preserves the sum of their weights, including degenerate intervals. -/
theorem closedInterval_indicator_relation {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (w : ι → ℚ) (hab : ∀ i, a i ≤ b i)
    (h : ∀ x : ℝ, (∑ i, if a i ≤ x ∧ x ≤ b i then w i else 0) = 0) :
    (∑ i, w i) = 0 := by
  classical
  have hgroup (r : ℝ) : (∑ i ∈ Finset.univ.filter (fun i => b i = r), w i) = 0 := by
    obtain ⟨t, hrt, hgap⟩ := exists_right_gap
      ((Finset.univ.image a) ∪ (Finset.univ.image b)) r
    have hdiff (i : ι) :
        (if a i ≤ r ∧ r ≤ b i then w i else 0) -
        (if a i ≤ t ∧ t ≤ b i then w i else 0) =
        if b i = r then w i else 0 := by
      by_cases hbr : b i = r
      · have hai : a i ≤ r := hbr ▸ hab i
        simp [hbr, hai, not_le_of_gt hrt]
      · by_cases hbi : b i < r
        · have hbt : b i < t := hbi.trans hrt
          simp [hbr, not_le_of_gt hbi, not_le_of_gt hbt]
        · have hrb : r < b i := lt_of_le_of_ne (le_of_not_gt hbi) (Ne.symm hbr)
          have htb : t < b i := hgap (b i)
            (mem_union_right _ (mem_image_of_mem b (mem_univ i))) hrb
          by_cases hai : a i ≤ r
          · have hat : a i ≤ t := hai.trans hrt.le
            simp [hbr, hai, hat, hrb.le, htb.le]
          · have hra : r < a i := lt_of_not_ge hai
            have hta : t < a i := hgap (a i)
              (mem_union_left _ (mem_image_of_mem a (mem_univ i))) hra
            simp [hbr, hai, not_le_of_gt hta]
    rw [Finset.sum_filter]
    calc
      _ = ∑ i, ((if a i ≤ r ∧ r ≤ b i then w i else 0) -
          (if a i ≤ t ∧ t ≤ b i then w i else 0)) :=
        Finset.sum_congr rfl (fun i _ => (hdiff i).symm)
      _ = 0 := by rw [Finset.sum_sub_distrib, h r, h t, sub_self]
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset ι)) (t := Finset.univ.image b) (g := b)
    (fun i hi => mem_image_of_mem b hi) w
  rw [← hf]
  exact Finset.sum_eq_zero (fun r _ => hgroup r)

end MagicSquaresEuler

/-! From CompactRealValuation.lean -/
set_option autoImplicit false

namespace MagicSquaresEuler

attribute [local instance] Classical.propDecidable

/-- The one-dimensional Euler relation, allowing empty compact convex sets. -/
theorem compactReal_indicator_relation {ι : Type*} [Fintype ι]
    (K : ι → Set ℝ) (w : ι → ℚ)
    (hc : ∀ i, IsCompact (K i)) (hv : ∀ i, Convex ℝ (K i))
    (h : ∀ x : ℝ, (∑ i, if x ∈ K i then w i else 0) = 0) :
    (∑ i, if (K i).Nonempty then w i else 0) = 0 := by
  classical
  let a : ι → ℝ := fun i => if (K i).Nonempty then sInf (K i) else 0
  let b : ι → ℝ := fun i => if (K i).Nonempty then sSup (K i) else 0
  let v : ι → ℚ := fun i => if (K i).Nonempty then w i else 0
  have hK (i : ι) (hi : (K i).Nonempty) : K i = Set.Icc (a i) (b i) := by
    simpa [a, b, hi] using eq_Icc_of_connected_compact ((hv i).isConnected hi) (hc i)
  have hab (i : ι) : a i ≤ b i := by
    by_cases hi : (K i).Nonempty
    · exact Set.nonempty_Icc.mp ((hK i hi) ▸ hi)
    · simp [a, b, hi]
  apply closedInterval_indicator_relation a b v hab
  intro x
  convert h x using 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (K i).Nonempty
  · simp only [v, if_pos hi]
    rw [hK i hi]
    simp only [Set.mem_Icc]
  · have hx : x ∉ K i := fun hx => hi ⟨x, hx⟩
    simp [v, hi, hx]

end MagicSquaresEuler

/-! From CompactConvexProjection.lean -/
set_option autoImplicit false

namespace MagicSquaresEuler

attribute [local instance] Classical.propDecidable

theorem compact_coordinateProjection (n : ℕ) (K : Set (Fin (n + 1) → ℝ))
    (hK : IsCompact K) : IsCompact ((fun x => x 0) '' K) :=
  hK.image (continuous_apply 0)

theorem convex_coordinateProjection (n : ℕ) (K : Set (Fin (n + 1) → ℝ))
    (hK : Convex ℝ K) : Convex ℝ ((fun x => x 0) '' K) :=
  hK.linear_image (LinearMap.proj 0)

/-- In dimension zero there is one point, so the relation follows by evaluation. -/
theorem zeroDim_indicator_relation {ι : Type*} [Fintype ι]
    (K : ι → Set (Fin 0 → ℝ)) (w : ι → ℚ)
    (h : ∀ x, (∑ i, if x ∈ K i then w i else 0) = 0) :
    (∑ i, if (K i).Nonempty then w i else 0) = 0 := by
  classical
  have heq (i : ι) : (K i).Nonempty ↔ (fun _ => (0 : ℝ)) ∈ K i := by
    constructor
    · rintro ⟨x, hx⟩
      have hx0 : x = fun _ => (0 : ℝ) := Subsingleton.elim _ _
      simpa only [hx0] using hx
    · intro hi
      exact ⟨_, hi⟩
  simpa only [heq] using h (fun _ => 0)

end MagicSquaresEuler

/-! From CompactConvexSlices.lean -/
set_option autoImplicit false

namespace MagicSquaresEuler

/-- The slice of a set in `n + 1` coordinates obtained by fixing coordinate
zero to be `t`. -/
def coordinateSlice (n : ℕ) (K : Set (Fin (n + 1) → ℝ)) (t : ℝ) :
    Set (Fin n → ℝ) :=
  {y | Fin.cons t y ∈ K}

theorem compact_coordinateSlice (n : ℕ) (K : Set (Fin (n + 1) → ℝ))
    (t : ℝ) (hK : IsCompact K) : IsCompact (coordinateSlice n K t) := by
  have hclosed : IsClosed {x : Fin (n + 1) → ℝ | x 0 = t} := by
    exact isClosed_singleton.preimage (continuous_apply 0)
  have heq : coordinateSlice n K t =
      (fun x : Fin (n + 1) → ℝ => Fin.tail x) ''
        (K ∩ {x : Fin (n + 1) → ℝ | x 0 = t}) := by
    ext y
    constructor
    · intro hy
      refine ⟨Fin.cons t y, ⟨hy, ?_⟩, ?_⟩
      · simp
      · simp
    · rintro ⟨x, ⟨hxK, hx0⟩, rfl⟩
      have hx : Fin.cons t (Fin.tail x) = x := by
        rw [← hx0]
        exact Fin.cons_self_tail x
      change Fin.cons t (Fin.tail x) ∈ K
      rwa [hx]
  rw [heq]
  exact (hK.inter_right hclosed).image continuous_id.finTail

theorem convex_coordinateSlice (n : ℕ) (K : Set (Fin (n + 1) → ℝ))
    (t : ℝ) (hK : Convex ℝ K) : Convex ℝ (coordinateSlice n K t) := by
  intro x hx y hy a b ha hb hab
  have hmem := hK hx hy ha hb hab
  show Fin.cons t (a • x + b • y) ∈ K
  convert hmem using 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← add_mul, hab, one_mul]
  · simp

theorem slice_nonempty_iff (n : ℕ) (K : Set (Fin (n + 1) → ℝ)) (t : ℝ) :
    (coordinateSlice n K t).Nonempty ↔ t ∈ (fun x => x 0) '' K := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨Fin.cons t y, hy, by simp⟩
  · rintro ⟨x, hxK, hx0⟩
    refine ⟨Fin.tail x, ?_⟩
    have hx : Fin.cons t (Fin.tail x) = x := by
      rw [← hx0]
      exact Fin.cons_self_tail x
    change Fin.cons t (Fin.tail x) ∈ K
    rwa [hx]

end MagicSquaresEuler

/-! From CompactConvexValuation.lean -/
set_option autoImplicit false

namespace MagicSquaresEuler

attribute [local instance] Classical.propDecidable

/-- Euler integration is well-defined on finite rational linear combinations
of compact convex indicators in every finite real coordinate space. -/
theorem compactConvex_indicator_relation (n : ℕ)
    {ι : Type*} [Fintype ι] (K : ι → Set (Fin n → ℝ)) (w : ι → ℚ)
    (hc : ∀ i, IsCompact (K i)) (hv : ∀ i, Convex ℝ (K i))
    (h : ∀ x, (∑ i, if x ∈ K i then w i else 0) = 0) :
    (∑ i, if (K i).Nonempty then w i else 0) = 0 := by
  classical
  induction n generalizing ι with
  | zero => exact zeroDim_indicator_relation K w h
  | succ n ih =>
    let P : ι → Set ℝ := fun i => (fun x => x 0) '' K i
    have hp : ∀ t : ℝ, (∑ i, if t ∈ P i then w i else 0) = 0 := by
      intro t
      have hs := ih (fun i => coordinateSlice n (K i) t) w
        (fun i => compact_coordinateSlice n (K i) t (hc i))
        (fun i => convex_coordinateSlice n (K i) t (hv i))
        (fun y => h (Fin.cons t y))
      simpa only [slice_nonempty_iff, P] using hs
    have htotal := compactReal_indicator_relation P w
      (fun i => compact_coordinateProjection n (K i) (hc i))
      (fun i => convex_coordinateProjection n (K i) (hv i)) hp
    simpa only [P, Set.image_nonempty] using htotal

end MagicSquaresEuler


theorem solution (n : ℕ)
    {ι : Type*} [Fintype ι] (K : ι → Set (Fin n → ℝ)) (w : ι → ℚ)
    (hc : ∀ i, IsCompact (K i)) (hv : ∀ i, Convex ℝ (K i))
    (h : ∀ x, (∑ i, if x ∈ K i then w i else 0) = 0) :
    (∑ i, if (K i).Nonempty then w i else 0) = 0 := by
  exact MagicSquaresEuler.compactConvex_indicator_relation n K w hc hv h
