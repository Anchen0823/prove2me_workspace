import Mathlib

namespace Chk_complete_parametrization

theorem solution {a b c d : ℤ} (h : a^2 + b^2 = c^2 + d^2) :
    (∃ p q r s : ℤ,
      a = p * r + q * s ∧ b = p * s - q * r ∧
        c = p * r - q * s ∧ d = p * s + q * r) ∨
      (∃ p q r s : ℤ,
        a = p * r + q * s ∧ b = p * s - q * r ∧
          d = p * r - q * s ∧ c = p * s + q * r) := by
  -- ------------------------------------------------------------------ parity
  have parity (a b c d : ℤ) (h : a^2 + b^2 = c^2 + d^2) :
      (Even (a - c) ∧ Even (b - d)) ∨ (Even (a - d) ∧ Even (b - c)) := by
    have ee {x y : ℤ} (hx : Even x) (hy : Even y) : Even (x - y) := by
      rcases hx with ⟨i, hi⟩
      rcases hy with ⟨j, hj⟩
      use i - j
      omega
    have oo {x y : ℤ} (hx : Odd x) (hy : Odd y) : Even (x - y) := by
      rcases hx with ⟨i, hi⟩
      rcases hy with ⟨j, hj⟩
      use i - j
      omega
    have sqmod4_even {x : ℤ} (hx : Even x) : (4 : ℤ) ∣ x^2 := by
      rcases hx with ⟨k, hk⟩
      use k^2
      rw [hk]
      ring
    have sqmod4_odd {x : ℤ} (hx : Odd x) : (4 : ℤ) ∣ x^2 - 1 := by
      rcases hx with ⟨k, hk⟩
      use k * (k + 1)
      rw [hk]
      ring
    have clash (rx ry rz rw : ℤ)
        (ha4 : (4 : ℤ) ∣ a^2 - rx) (hb4 : (4 : ℤ) ∣ b^2 - ry)
        (hc4 : (4 : ℤ) ∣ c^2 - rz) (hd4 : (4 : ℤ) ∣ d^2 - rw)
        (hneq : rx + ry ≠ rz + rw)
        (hsmall : -4 < rz + rw - rx - ry ∧ rz + rw - rx - ry < 4) : False := by
      have hdiv : (4 : ℤ) ∣ (a^2 - rx) + (b^2 - ry) - (c^2 - rz) - (d^2 - rw) :=
        dvd_sub (dvd_sub (dvd_add ha4 hb4) hc4) hd4
      have hval : (a^2 - rx) + (b^2 - ry) - (c^2 - rz) - (d^2 - rw) = rz + rw - rx - ry := by
        nlinarith
      rw [hval] at hdiv
      rcases hdiv with ⟨t, ht⟩
      omega
    rcases Int.even_or_odd a with ha | ha <;>
    rcases Int.even_or_odd b with hb | hb <;>
    rcases Int.even_or_odd c with hc | hc <;>
    rcases Int.even_or_odd d with hd | hd
    · exact Or.inl ⟨ee ha hc, ee hb hd⟩
    · exfalso
      exact clash 0 0 0 1 (by simpa using sqmod4_even ha) (by simpa using sqmod4_even hb)
        (by simpa using sqmod4_even hc) (sqmod4_odd hd) (by norm_num) (by norm_num)
    · exfalso
      exact clash 0 0 1 0 (by simpa using sqmod4_even ha) (by simpa using sqmod4_even hb)
        (sqmod4_odd hc) (by simpa using sqmod4_even hd) (by norm_num) (by norm_num)
    · exfalso
      exact clash 0 0 1 1 (by simpa using sqmod4_even ha) (by simpa using sqmod4_even hb)
        (sqmod4_odd hc) (sqmod4_odd hd) (by norm_num) (by norm_num)
    · exfalso
      exact clash 0 1 0 0 (by simpa using sqmod4_even ha) (sqmod4_odd hb)
        (by simpa using sqmod4_even hc) (by simpa using sqmod4_even hd) (by norm_num) (by norm_num)
    · exact Or.inl ⟨ee ha hc, oo hb hd⟩
    · exact Or.inr ⟨ee ha hd, oo hb hc⟩
    · exfalso
      exact clash 0 1 1 1 (by simpa using sqmod4_even ha) (sqmod4_odd hb)
        (sqmod4_odd hc) (sqmod4_odd hd) (by norm_num) (by norm_num)
    · exfalso
      exact clash 1 0 0 0 (sqmod4_odd ha) (by simpa using sqmod4_even hb)
        (by simpa using sqmod4_even hc) (by simpa using sqmod4_even hd) (by norm_num) (by norm_num)
    · exact Or.inr ⟨oo ha hd, ee hb hc⟩
    · exact Or.inl ⟨oo ha hc, ee hb hd⟩
    · exfalso
      exact clash 1 0 1 1 (sqmod4_odd ha) (by simpa using sqmod4_even hb)
        (sqmod4_odd hc) (sqmod4_odd hd) (by norm_num) (by norm_num)
    · exfalso
      exact clash 1 1 0 0 (sqmod4_odd ha) (sqmod4_odd hb)
        (by simpa using sqmod4_even hc) (by simpa using sqmod4_even hd) (by norm_num) (by norm_num)
    · exfalso
      exact clash 1 1 0 1 (sqmod4_odd ha) (sqmod4_odd hb)
        (by simpa using sqmod4_even hc) (sqmod4_odd hd) (by norm_num) (by norm_num)
    · exfalso
      exact clash 1 1 1 0 (sqmod4_odd ha) (sqmod4_odd hb)
        (sqmod4_odd hc) (by simpa using sqmod4_even hd) (by norm_num) (by norm_num)
    · exact Or.inl ⟨oo ha hc, oo hb hd⟩
  -- ------------------------------------------------------------------ halves
  have halves (a b c d : ℤ) (h : a^2 + b^2 = c^2 + d^2)
      (hac : Even (a - c)) (hbd : Even (b - d)) :
      ∃ X Y U V : ℤ,
        X + Y = a ∧ X - Y = c ∧ U - V = b ∧ U + V = d ∧ X * Y = U * V := by
    rcases hac with ⟨k, hk⟩
    rcases hbd with ⟨l, hl⟩
    have hc : c = a - 2 * k := by linarith
    have hd : d = b - 2 * l := by linarith
    rw [hc, hd] at h ⊢
    refine ⟨a - k, k, b - l, -l, ?_, ?_, ?_, ?_, ?_⟩
    · ring
    · ring
    · ring
    · ring
    · nlinarith
  -- ------------------------------------------------------------------ factor
  have factor (X Y U V : ℤ) (h : X * Y = U * V) :
      ∃ p q r s : ℤ, X = p * r ∧ Y = q * s ∧ U = p * s ∧ V = q * r := by
    by_cases hX : X = 0
    · by_cases hU : U = 0
      · refine ⟨0, 1, V, Y, ?_, ?_, ?_, ?_⟩ <;> simp [hX, hU]
      · have hV : V = 0 := by
          have h' := h
          rw [hX] at h'
          have hUV : U * V = 0 := by simpa using h'.symm
          exact (mul_eq_zero.mp hUV).resolve_left hU
        refine ⟨U, Y, 0, 1, ?_, ?_, ?_, ?_⟩ <;> simp [hX, hV]
    · by_cases hU : U = 0
      · have hY : Y = 0 := by
          have h' := h
          rw [hU] at h'
          have hXY : X * Y = 0 := by simpa using h'
          exact (mul_eq_zero.mp hXY).resolve_left hX
        refine ⟨X, V, 1, 0, ?_, ?_, ?_, ?_⟩ <;> simp [hU, hY]
      · have hgpos : 0 < Int.gcd X U := Int.gcd_pos_of_ne_zero_left U hX
        let g : ℤ := (Int.gcd X U : ℤ)
        obtain ⟨r, s, hcop, hXeq0, hUeq0⟩ := Int.exists_gcd_one (m := X) (n := U) hgpos
        have hXeq : X = r * g := by simpa [g] using hXeq0
        have hUeq : U = s * g := by simpa [g] using hUeq0
        have hgne : g ≠ 0 := by
          dsimp [g]
          exact_mod_cast (ne_of_gt hgpos)
        have hmul : g * (r * Y) = g * (s * V) := by
          calc
            g * (r * Y) = (r * g) * Y := by ring
            _ = X * Y := by rw [← hXeq]
            _ = U * V := h
            _ = (s * g) * V := by rw [hUeq]
            _ = g * (s * V) := by ring
        have hrY : r * Y = s * V := mul_left_cancel₀ hgne hmul
        have hr_ne : r ≠ 0 := by
          intro hr
          apply hX
          calc
            X = r * g := hXeq
            _ = 0 := by rw [hr]; ring
        have hs_ne : s ≠ 0 := by
          intro hs
          apply hU
          calc
            U = s * g := hUeq
            _ = 0 := by rw [hs]; ring
        have hbez : (1 : ℤ) = r * Int.gcdA r s + s * Int.gcdB r s := by
          have := Int.gcd_eq_gcd_ab r s
          simpa [hcop] using this
        have hsry : s ∣ r * Y := ⟨V, hrY⟩
        have hrsv : r ∣ s * V := ⟨Y, hrY.symm⟩
        have hsY : s ∣ Y := by
          have h1 : s ∣ (r * Y) * Int.gcdA r s := dvd_mul_of_dvd_left hsry _
          have h2 : s ∣ s * (Y * Int.gcdB r s) := dvd_mul_right s _
          have hsum := dvd_add h1 h2
          have heq : (r * Y) * Int.gcdA r s + s * (Y * Int.gcdB r s) = Y := by
            calc
              (r * Y) * Int.gcdA r s + s * (Y * Int.gcdB r s) =
                  Y * (r * Int.gcdA r s + s * Int.gcdB r s) := by ring
              _ = Y * 1 := by rw [hbez]
              _ = Y := by ring
          rwa [heq] at hsum
        have hrV : r ∣ V := by
          have h1 : r ∣ r * (V * Int.gcdA r s) := dvd_mul_right r _
          have h2 : r ∣ (s * V) * Int.gcdB r s := dvd_mul_of_dvd_left hrsv _
          have hsum := dvd_add h1 h2
          have heq : r * (V * Int.gcdA r s) + (s * V) * Int.gcdB r s = V := by
            calc
              r * (V * Int.gcdA r s) + (s * V) * Int.gcdB r s =
                  V * (r * Int.gcdA r s + s * Int.gcdB r s) := by ring
              _ = V * 1 := by rw [hbez]
              _ = V := by ring
          rwa [heq] at hsum
        rcases hsY with ⟨q, hq⟩
        rcases hrV with ⟨q', hq'⟩
        have hqq : q = q' := by
          have hmain : r * s * q = r * s * q' := by
            calc
              r * s * q = r * (s * q) := by ring
              _ = r * Y := by rw [← hq]
              _ = s * V := hrY
              _ = s * (r * q') := by rw [hq']
              _ = r * s * q' := by ring
          exact mul_left_cancel₀ (mul_ne_zero hr_ne hs_ne) hmain
        refine ⟨g, q, r, s, ?_, ?_, ?_, ?_⟩
        · calc
            X = r * g := hXeq
            _ = g * r := by ring
        · rw [hq]
          ring
        · calc
            U = s * g := hUeq
            _ = g * s := by ring
        · rw [hq', ← hqq]
          ring
  -- ------------------------------------------------------------------ assembly
  rcases parity a b c d h with hleft | hright
  · rcases hleft with ⟨hac, hbd⟩
    obtain ⟨X, Y, U, V, hXa, hXc, hUb, hUd, hprod⟩ := halves a b c d h hac hbd
    obtain ⟨p, q, r, s, hpr, hqs, hps, hqr⟩ := factor X Y U V hprod
    left
    refine ⟨p, q, r, s, ?_, ?_, ?_, ?_⟩
    · calc
        a = X + Y := hXa.symm
        _ = p * r + q * s := by rw [hpr, hqs]
    · calc
        b = U - V := hUb.symm
        _ = p * s - q * r := by rw [hps, hqr]
    · calc
        c = X - Y := hXc.symm
        _ = p * r - q * s := by rw [hpr, hqs]
    · calc
        d = U + V := hUd.symm
        _ = p * s + q * r := by rw [hps, hqr]
  · rcases hright with ⟨had, hbc⟩
    have h' : a^2 + b^2 = d^2 + c^2 := by nlinarith
    obtain ⟨X, Y, U, V, hXa, hXd, hUb, hUc, hprod⟩ := halves a b d c h' had hbc
    obtain ⟨p, q, r, s, hpr, hqs, hps, hqr⟩ := factor X Y U V hprod
    right
    refine ⟨p, q, r, s, ?_, ?_, ?_, ?_⟩
    · calc
        a = X + Y := hXa.symm
        _ = p * r + q * s := by rw [hpr, hqs]
    · calc
        b = U - V := hUb.symm
        _ = p * s - q * r := by rw [hps, hqr]
    · calc
        d = X - Y := hXd.symm
        _ = p * r - q * s := by rw [hpr, hqs]
    · calc
        c = U + V := hUc.symm
        _ = p * s + q * r := by rw [hps, hqr]

end Chk_complete_parametrization

namespace Chk_explicit_family_chain

theorem solution {n : ℤ} (hn : 4 ≤ n) :
    (1 : ℤ) < 2 * n - 1 ∧
      2 * n - 1 < n^2 - n - 1 ∧
        n^2 - n - 1 < n^2 - n + 1 := by
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

end Chk_explicit_family_chain

namespace Chk_explicit_family_identity

theorem solution (n : ℤ) :
    (1 : ℤ)^2 + (n^2 - n + 1)^2 = (2 * n - 1)^2 + (n^2 - n - 1)^2 := by
  ring

end Chk_explicit_family_identity

namespace Chk_explicit_family_solution

theorem solution {n : ℤ} (hn : 4 ≤ n) :
    (1 : ℤ)^2 + (n^2 - n + 1)^2 = (2 * n - 1)^2 + (n^2 - n - 1)^2 ∧
      (0 < (1 : ℤ) ∧ 0 < n^2 - n + 1 ∧ 0 < 2 * n - 1 ∧ 0 < n^2 - n - 1) ∧
        ((1 : ℤ) ≠ 2 * n - 1 ∧
          (1 : ℤ) ≠ n^2 - n - 1 ∧
            (1 : ℤ) ≠ n^2 - n + 1 ∧
              2 * n - 1 ≠ n^2 - n - 1 ∧
                2 * n - 1 ≠ n^2 - n + 1 ∧
                  n^2 - n - 1 ≠ n^2 - n + 1) := by
  have h1 : (1 : ℤ) < 2 * n - 1 := by nlinarith
  have h2 : 2 * n - 1 < n^2 - n - 1 := by nlinarith
  have h3 : n^2 - n - 1 < n^2 - n + 1 := by nlinarith
  have h12 : (1 : ℤ) < n^2 - n - 1 := lt_trans h1 h2
  have h13 : (1 : ℤ) < n^2 - n + 1 := lt_trans h12 h3
  have h23 : 2 * n - 1 < n^2 - n + 1 := lt_trans h2 h3
  constructor
  · ring
  constructor
  · exact ⟨by norm_num, by linarith, by linarith, by linarith⟩
  · exact ⟨ne_of_lt h1, ne_of_lt h12, ne_of_lt h13,
      ne_of_lt h2, ne_of_lt h23, ne_of_lt h3⟩

end Chk_explicit_family_solution

namespace Chk_family_patterns_infinite

theorem solution :
    (Set.range (fun n : ℤ => ((1 : ℤ), n^2 - n + 1, 2 * n - 1, n^2 - n - 1))).Infinite := by
  apply Set.infinite_range_of_injective
  intro m n h
  have hlin : 2 * m - 1 = 2 * n - 1 := by
    simpa using congrArg (fun t : ℤ × ℤ × ℤ × ℤ => t.2.2.1) h
  omega

end Chk_family_patterns_infinite

namespace Chk_family_scaling_trivial

theorem solution {m n k : ℤ}
    (h : ((1 : ℤ), n^2 - n + 1, 2 * n - 1, n^2 - n - 1) =
      k • ((1 : ℤ), m^2 - m + 1, 2 * m - 1, m^2 - m - 1)) :
    n = m := by
  have hk : k = 1 := by
    have hcoord := congrArg (fun t : ℤ × ℤ × ℤ × ℤ => t.1) h
    simpa using hcoord.symm
  have hunit : ((1 : ℤ), n^2 - n + 1, 2 * n - 1, n^2 - n - 1) =
      ((1 : ℤ), m^2 - m + 1, 2 * m - 1, m^2 - m - 1) := by
    rw [hk] at h
    simpa using h
  have hlin : 2 * n - 1 = 2 * m - 1 := by
    simpa using congrArg (fun t : ℤ × ℤ × ℤ × ℤ => t.2.2.1) hunit
  omega

end Chk_family_scaling_trivial

namespace Chk_familyQuad_injective

theorem solution :
    Function.Injective
      (fun n : ℤ => ((1 : ℤ), n^2 - n + 1, 2 * n - 1, n^2 - n - 1)) := by
  intro m n h
  have hlin : 2 * m - 1 = 2 * n - 1 := by
    simpa using congrArg (fun t : ℤ × ℤ × ℤ × ℤ => t.2.2.1) h
  omega

end Chk_familyQuad_injective

namespace Chk_four_factor_param

theorem solution (X Y U V : ℤ) (h : X * Y = U * V) :
    ∃ p q r s : ℤ, X = p * r ∧ Y = q * s ∧ U = p * s ∧ V = q * r := by
  by_cases hX : X = 0
  · by_cases hU : U = 0
    · refine ⟨0, 1, V, Y, ?_, ?_, ?_, ?_⟩ <;> simp [hX, hU]
    · have hV : V = 0 := by
        have h' := h
        rw [hX] at h'
        have hUV : U * V = 0 := by simpa using h'.symm
        exact (mul_eq_zero.mp hUV).resolve_left hU
      refine ⟨U, Y, 0, 1, ?_, ?_, ?_, ?_⟩ <;> simp [hX, hV]
  · by_cases hU : U = 0
    · have hY : Y = 0 := by
        have h' := h
        rw [hU] at h'
        have hXY : X * Y = 0 := by simpa using h'
        exact (mul_eq_zero.mp hXY).resolve_left hX
      refine ⟨X, V, 1, 0, ?_, ?_, ?_, ?_⟩ <;> simp [hU, hY]
    · have hgpos : 0 < Int.gcd X U := Int.gcd_pos_of_ne_zero_left U hX
      let g : ℤ := (Int.gcd X U : ℤ)
      obtain ⟨r, s, hcop, hXeq0, hUeq0⟩ := Int.exists_gcd_one (m := X) (n := U) hgpos
      have hXeq : X = r * g := by simpa [g] using hXeq0
      have hUeq : U = s * g := by simpa [g] using hUeq0
      have hgne : g ≠ 0 := by
        dsimp [g]
        exact_mod_cast (ne_of_gt hgpos)
      -- Cancel the nonzero gcd from X*Y = U*V after substituting X = r*g and U = s*g.
      have hmul : g * (r * Y) = g * (s * V) := by
        calc
          g * (r * Y) = (r * g) * Y := by ring
          _ = X * Y := by rw [← hXeq]
          _ = U * V := h
          _ = (s * g) * V := by rw [hUeq]
          _ = g * (s * V) := by ring
      have hrY : r * Y = s * V := mul_left_cancel₀ hgne hmul
      have hr_ne : r ≠ 0 := by
        intro hr
        apply hX
        calc
          X = r * g := hXeq
          _ = 0 := by rw [hr]; ring
      have hs_ne : s ≠ 0 := by
        intro hs
        apply hU
        calc
          U = s * g := hUeq
          _ = 0 := by rw [hs]; ring
      -- Bezout for the coprime pair (r, s): 1 = r*A + s*B.
      have hbez : (1 : ℤ) = r * Int.gcdA r s + s * Int.gcdB r s := by
        have := Int.gcd_eq_gcd_ab r s
        simpa [hcop] using this
      have hsry : s ∣ r * Y := ⟨V, hrY⟩
      have hrsv : r ∣ s * V := ⟨Y, hrY.symm⟩
      have hsY : s ∣ Y := by
        have h1 : s ∣ (r * Y) * Int.gcdA r s := dvd_mul_of_dvd_left hsry _
        have h2 : s ∣ s * (Y * Int.gcdB r s) := dvd_mul_right s _
        have hsum := dvd_add h1 h2
        have heq : (r * Y) * Int.gcdA r s + s * (Y * Int.gcdB r s) = Y := by
          calc
            (r * Y) * Int.gcdA r s + s * (Y * Int.gcdB r s) =
                Y * (r * Int.gcdA r s + s * Int.gcdB r s) := by ring
            _ = Y * 1 := by rw [hbez]
            _ = Y := by ring
        rwa [heq] at hsum
      have hrV : r ∣ V := by
        have h1 : r ∣ r * (V * Int.gcdA r s) := dvd_mul_right r _
        have h2 : r ∣ (s * V) * Int.gcdB r s := dvd_mul_of_dvd_left hrsv _
        have hsum := dvd_add h1 h2
        have heq : r * (V * Int.gcdA r s) + (s * V) * Int.gcdB r s = V := by
          calc
            r * (V * Int.gcdA r s) + (s * V) * Int.gcdB r s =
                V * (r * Int.gcdA r s + s * Int.gcdB r s) := by ring
            _ = V * 1 := by rw [hbez]
            _ = V := by ring
        rwa [heq] at hsum
      rcases hsY with ⟨q, hq⟩
      rcases hrV with ⟨q', hq'⟩
      have hqq : q = q' := by
        have hmain : r * s * q = r * s * q' := by
          calc
            r * s * q = r * (s * q) := by ring
            _ = r * Y := by rw [← hq]
            _ = s * V := hrY
            _ = s * (r * q') := by rw [hq']
            _ = r * s * q' := by ring
        exact mul_left_cancel₀ (mul_ne_zero hr_ne hs_ne) hmain
      refine ⟨g, q, r, s, ?_, ?_, ?_, ?_⟩
      · calc
          X = r * g := hXeq
          _ = g * r := by ring
      · rw [hq]
        ring
      · calc
          U = s * g := hUeq
          _ = g * s := by ring
      · rw [hq', ← hqq]
        ring

end Chk_four_factor_param

namespace Chk_four_param_identity

theorem solution (p q r s : ℤ) :
    (p * r + q * s)^2 + (p * s - q * r)^2 =
      (p * r - q * s)^2 + (p * s + q * r)^2 := by
  ring

end Chk_four_param_identity

namespace Chk_parity_alignment

theorem solution {a b c d : ℤ} (h : a^2 + b^2 = c^2 + d^2) :
    (Even (a - c) ∧ Even (b - d)) ∨ (Even (a - d) ∧ Even (b - c)) := by
  -- Two ways of subtracting parities. Both are read off from witnesses, so no parity
  -- lemma library is needed.
  have ee {x y : ℤ} (hx : Even x) (hy : Even y) : Even (x - y) := by
    rcases hx with ⟨i, hi⟩
    rcases hy with ⟨j, hj⟩
    use i - j
    omega
  have oo {x y : ℤ} (hx : Odd x) (hy : Odd y) : Even (x - y) := by
    rcases hx with ⟨i, hi⟩
    rcases hy with ⟨j, hj⟩
    use i - j
    omega
  -- A square is 0 or 1 modulo 4 according to the parity of its root.
  have sqmod4_even {x : ℤ} (hx : Even x) : (4 : ℤ) ∣ x^2 := by
    rcases hx with ⟨k, hk⟩
    use k^2
    rw [hk]
    ring
  have sqmod4_odd {x : ℤ} (hx : Odd x) : (4 : ℤ) ∣ x^2 - 1 := by
    rcases hx with ⟨k, hk⟩
    use k * (k + 1)
    rw [hk]
    ring
  -- If the four residues rx,ry,rz,rw (each 0 or 1) do not satisfy rx+ry = rz+rw, then
  -- the equation is impossible: subtracting the residues shows 4 divides rz+rw-rx-ry,
  -- which lies strictly between -4 and 4 and is nonzero.
  have clash (rx ry rz rw : ℤ)
      (ha4 : (4 : ℤ) ∣ a^2 - rx) (hb4 : (4 : ℤ) ∣ b^2 - ry)
      (hc4 : (4 : ℤ) ∣ c^2 - rz) (hd4 : (4 : ℤ) ∣ d^2 - rw)
      (hneq : rx + ry ≠ rz + rw)
      (hsmall : -4 < rz + rw - rx - ry ∧ rz + rw - rx - ry < 4) : False := by
    have hdiv : (4 : ℤ) ∣ (a^2 - rx) + (b^2 - ry) - (c^2 - rz) - (d^2 - rw) :=
      dvd_sub (dvd_sub (dvd_add ha4 hb4) hc4) hd4
    have hval : (a^2 - rx) + (b^2 - ry) - (c^2 - rz) - (d^2 - rw) = rz + rw - rx - ry := by
      nlinarith
    rw [hval] at hdiv
    rcases hdiv with ⟨t, ht⟩
    omega
  rcases Int.even_or_odd a with ha | ha <;>
  rcases Int.even_or_odd b with hb | hb <;>
  rcases Int.even_or_odd c with hc | hc <;>
  rcases Int.even_or_odd d with hd | hd
  · exact Or.inl ⟨ee ha hc, ee hb hd⟩
  · exfalso
    exact clash 0 0 0 1 (by simpa using sqmod4_even ha) (by simpa using sqmod4_even hb)
      (by simpa using sqmod4_even hc) (sqmod4_odd hd) (by norm_num) (by norm_num)
  · exfalso
    exact clash 0 0 1 0 (by simpa using sqmod4_even ha) (by simpa using sqmod4_even hb)
      (sqmod4_odd hc) (by simpa using sqmod4_even hd) (by norm_num) (by norm_num)
  · exfalso
    exact clash 0 0 1 1 (by simpa using sqmod4_even ha) (by simpa using sqmod4_even hb)
      (sqmod4_odd hc) (sqmod4_odd hd) (by norm_num) (by norm_num)
  · exfalso
    exact clash 0 1 0 0 (by simpa using sqmod4_even ha) (sqmod4_odd hb)
      (by simpa using sqmod4_even hc) (by simpa using sqmod4_even hd) (by norm_num) (by norm_num)
  · exact Or.inl ⟨ee ha hc, oo hb hd⟩
  · exact Or.inr ⟨ee ha hd, oo hb hc⟩
  · exfalso
    exact clash 0 1 1 1 (by simpa using sqmod4_even ha) (sqmod4_odd hb)
      (sqmod4_odd hc) (sqmod4_odd hd) (by norm_num) (by norm_num)
  · exfalso
    exact clash 1 0 0 0 (sqmod4_odd ha) (by simpa using sqmod4_even hb)
      (by simpa using sqmod4_even hc) (by simpa using sqmod4_even hd) (by norm_num) (by norm_num)
  · exact Or.inr ⟨oo ha hd, ee hb hc⟩
  · exact Or.inl ⟨oo ha hc, ee hb hd⟩
  · exfalso
    exact clash 1 0 1 1 (sqmod4_odd ha) (by simpa using sqmod4_even hb)
      (sqmod4_odd hc) (sqmod4_odd hd) (by norm_num) (by norm_num)
  · exfalso
    exact clash 1 1 0 0 (sqmod4_odd ha) (sqmod4_odd hb)
      (by simpa using sqmod4_even hc) (by simpa using sqmod4_even hd) (by norm_num) (by norm_num)
  · exfalso
    exact clash 1 1 0 1 (sqmod4_odd ha) (sqmod4_odd hb)
      (by simpa using sqmod4_even hc) (sqmod4_odd hd) (by norm_num) (by norm_num)
  · exfalso
    exact clash 1 1 1 0 (sqmod4_odd ha) (sqmod4_odd hb)
      (sqmod4_odd hc) (by simpa using sqmod4_even hd) (by norm_num) (by norm_num)
  · exact Or.inl ⟨oo ha hc, oo hb hd⟩

end Chk_parity_alignment

namespace Chk_sum_sq_eq_halves

theorem solution {a b c d : ℤ} (h : a^2 + b^2 = c^2 + d^2)
    (hac : Even (a - c)) (hbd : Even (b - d)) :
    ∃ X Y U V : ℤ,
      X + Y = a ∧ X - Y = c ∧ U - V = b ∧ U + V = d ∧ X * Y = U * V := by
  rcases hac with ⟨k, hk⟩
  rcases hbd with ⟨l, hl⟩
  have hc : c = a - 2 * k := by linarith
  have hd : d = b - 2 * l := by linarith
  rw [hc, hd] at h ⊢
  refine ⟨a - k, k, b - l, -l, ?_, ?_, ?_, ?_, ?_⟩
  · ring
  · ring
  · ring
  · ring
  · nlinarith

end Chk_sum_sq_eq_halves

namespace Chk_sum_sq_eq_iff_product

theorem solution (a b c d : ℤ) :
    a^2 + b^2 = c^2 + d^2 ↔ (a + c) * (a - c) = (d + b) * (d - b) := by
  constructor
  · intro h
    nlinarith [show (a + c) * (a - c) = a^2 - c^2 by ring,
      show (d + b) * (d - b) = d^2 - b^2 by ring]
  · intro h
    nlinarith [show (a + c) * (a - c) = a^2 - c^2 by ring,
      show (d + b) * (d - b) = d^2 - b^2 by ring]

end Chk_sum_sq_eq_iff_product

namespace Chk_two_squares_mul

theorem solution {R : Type*} [CommRing R] (p q r s : R) :
    (p^2 + q^2) * (r^2 + s^2) = (p * r + q * s)^2 + (p * s - q * r)^2 ∧
      (p^2 + q^2) * (r^2 + s^2) = (p * r - q * s)^2 + (p * s + q * r)^2 := by
  constructor <;> ring

end Chk_two_squares_mul

#print axioms Chk_complete_parametrization.solution
#print axioms Chk_explicit_family_chain.solution
#print axioms Chk_explicit_family_identity.solution
#print axioms Chk_explicit_family_solution.solution
#print axioms Chk_family_patterns_infinite.solution
#print axioms Chk_family_scaling_trivial.solution
#print axioms Chk_familyQuad_injective.solution
#print axioms Chk_four_factor_param.solution
#print axioms Chk_four_param_identity.solution
#print axioms Chk_parity_alignment.solution
#print axioms Chk_sum_sq_eq_halves.solution
#print axioms Chk_sum_sq_eq_iff_product.solution
#print axioms Chk_two_squares_mul.solution
