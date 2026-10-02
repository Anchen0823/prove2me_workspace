import Definitions.Def_KKBinPacking_GeometricGrouping_GeomGroup
import Definitions.Def_KKBinPacking_GeometricGrouping_Instance

open KKBinPacking.GeometricGrouping

namespace KKContribution

lemma takeUntil_append_drop (k : ℝ) (L : List ℝ) :
    takeUntil k L ++ L.drop (takeUntil k L).length = L := by
  induction L generalizing k with
  | nil => simp [takeUntil]
  | cons x xs ih =>
    rw [takeUntil]
    split_ifs with h
    · simp
    · simpa using congrArg (List.cons x) (ih (k - x))

lemma groups_sum (k : ℝ) : (L : List ℝ) →
    ((geomGroupsList k L).map (fun (G : List ℝ) => (G : Multiset ℝ))).sum =
      (L : Multiset ℝ)
  | [] => by simp [geomGroupsList]
  | x :: xs => by
    rw [geomGroupsList]
    simp only [List.map_cons, List.sum_cons]
    rw [groups_sum k ((x :: xs).drop (takeUntil k (x :: xs)).length)]
    rw [Multiset.coe_add, takeUntil_append_drop]
termination_by L => L.length
decreasing_by
  simp only [List.length_drop, List.length_cons]
  have := takeUntil_cons_length_pos k x xs
  omega

lemma adjacent_partition (A : List ℝ) (Gs : List (List ℝ)) :
    (List.zipWith
      (fun (Gprev Gi : List ℝ) =>
        (((Gi.take Gprev.length).map (fun p => (p, Gi.headD 0))) : Multiset (ℝ × ℝ)))
      (A :: Gs) Gs).sum.map Prod.fst +
    (List.zipWith (fun (Gprev Gi : List ℝ) => ((Gi.drop Gprev.length) : Multiset ℝ))
      (A :: Gs) Gs).sum = (Gs.map (fun (G : List ℝ) => (G : Multiset ℝ))).sum := by
  induction Gs generalizing A with
  | nil => simp
  | cons G Gs ih =>
    have hsplit :
      ((G.take A.length : List ℝ) : Multiset ℝ) + (G.drop A.length : List ℝ) =
      (G : Multiset ℝ) := by rw [Multiset.coe_add, List.take_append_drop]
    simp only [List.zipWith_cons_cons, List.sum_cons, Multiset.map_add,
      Multiset.map_coe, List.map_map, Function.comp_def, List.map_id']
    simp only [List.map_cons, List.sum_cons]
    calc
      _ = ((G.take A.length : List ℝ) : Multiset ℝ) + (G.drop A.length : List ℝ) +
        ((List.zipWith
          (fun (Gprev Gi : List ℝ) =>
            (((Gi.take Gprev.length).map (fun p => (p, Gi.headD 0))) : Multiset (ℝ × ℝ)))
          (G :: Gs) Gs).sum.map Prod.fst +
        (List.zipWith (fun (Gprev Gi : List ℝ) => ((Gi.drop Gprev.length) : Multiset ℝ))
          (G :: Gs) Gs).sum) := by abel
      _ = _ := by rw [hsplit, ih G]

lemma geom_partition (k : ℕ) (I : Multiset ℝ) :
    (geomPairs k I).map Prod.fst + geomJ' k I = I := by
  have hsum : ((geomGroups k I).map (fun (G : List ℝ) => (G : Multiset ℝ))).sum = I := by
    rw [geomGroups, groups_sum, Multiset.sort_eq]
  apply Eq.trans (b := ((geomGroups k I).map (fun (G : List ℝ) => (G : Multiset ℝ))).sum) ?_ hsum
  unfold geomPairs geomJ'
  generalize geomGroups k I = Gs
  cases Gs with
  | nil => simp
  | cons A Gs =>
    simp only [List.tail_cons, List.headD_cons, List.map_cons, List.sum_cons]
    rw [show
      (List.zipWith
        (fun (Gprev Gi : List ℝ) =>
          (((Gi.take Gprev.length).map (fun p => (p, Gi.headD 0))) : Multiset (ℝ × ℝ)))
        (A :: Gs) Gs).sum.map Prod.fst +
      ((A : Multiset ℝ) +
        (List.zipWith (fun (Gprev Gi : List ℝ) => ((Gi.drop Gprev.length) : Multiset ℝ))
          (A :: Gs) Gs).sum) =
      (A : Multiset ℝ) + ((Gs.map (fun (G : List ℝ) => (G : Multiset ℝ))).sum) by
        rw [← adjacent_partition A Gs]
        abel]

lemma groups_pairwise (k : ℝ) : (L : List ℝ) → L.Pairwise (· ≥ ·) →
    ∀ G ∈ geomGroupsList k L, G.Pairwise (· ≥ ·)
  | [], _ => by simp [geomGroupsList]
  | x :: xs, hL => by
    rw [geomGroupsList]
    intro G hG
    simp only [List.mem_cons] at hG
    rcases hG with rfl | hG
    · have h : (takeUntil k (x :: xs) ++
          (x :: xs).drop (takeUntil k (x :: xs)).length).Pairwise (· ≥ ·) := by
        rwa [takeUntil_append_drop]
      exact (List.pairwise_append.mp h).1
    · exact groups_pairwise k _ hL.drop G hG
termination_by L => L.length
decreasing_by
  simp only [List.length_drop, List.length_cons]
  have := takeUntil_cons_length_pos k x xs
  omega

lemma headD_ge {G : List ℝ} (hG : G.Pairwise (· ≥ ·)) {x : ℝ} (hx : x ∈ G) :
    x ≤ G.headD 0 := by
  cases G with
  | nil => simp at hx
  | cons y ys => simpa using hG.rel_head hx

lemma adjacent_pair_le (A : List ℝ) (Gs : List (List ℝ))
    (hsorted : ∀ G ∈ Gs, G.Pairwise (· ≥ ·)) :
    ∀ p ∈ (List.zipWith
      (fun (Gprev Gi : List ℝ) =>
        (((Gi.take Gprev.length).map (fun x => (x, Gi.headD 0))) : Multiset (ℝ × ℝ)))
      (A :: Gs) Gs).sum, p.1 ≤ p.2 := by
  induction Gs generalizing A with
  | nil => simp
  | cons G Gs ih =>
    intro p hp
    simp only [List.zipWith_cons_cons, List.sum_cons, Multiset.mem_add,
      Multiset.mem_coe, List.mem_map] at hp
    rcases hp with ⟨x, hx, rfl⟩ | hp
    · exact headD_ge (hsorted G (by simp)) (List.mem_of_mem_take hx)
    · exact ih G (fun H hH => hsorted H (by simp [hH])) p hp

lemma geom_pair_le (k : ℕ) (I : Multiset ℝ) :
    ∀ p ∈ geomPairs k I, p.1 ≤ p.2 := by
  have hsorted : ∀ G ∈ geomGroups k I, G.Pairwise (· ≥ ·) := by
    exact groups_pairwise (k : ℝ) _ (Multiset.pairwise_sort _ _)
  unfold geomPairs
  generalize geomGroups k I = Gs at *
  cases Gs with
  | nil => simp
  | cons A Gs =>
    simp only [List.tail_cons]
    exact adjacent_pair_le A Gs (fun G hG => hsorted G (by simp [hG]))

lemma fst_mem_source (k : ℕ) (I : Multiset ℝ) {p : ℝ × ℝ} (hp : p ∈ geomPairs k I) :
    p.1 ∈ I := by
  rw [← geom_partition k I]
  exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_map.mpr ⟨p, hp, rfl⟩))

end KKContribution
