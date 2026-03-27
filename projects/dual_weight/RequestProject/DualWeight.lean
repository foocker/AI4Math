/-
# Dual Weight Distribution of the Code C_{f,g}

Formalized verification of the claims about the dual weight distribution
of the binary minimal linear code from Theorem 4 / Table 3.

## Main results
1. Sum of multiplicities = 4q² (equivalently 2^m + 3q²).
2. The power-of-2 constraint forces m = 2t.
3. Table 3 has 7 nonzero weights (not 8 as the old draft claims).
4. A₁⊥ = 0 (first Pless power moment).
5. A₂⊥ = 0 (second Pless power moment).
6. Explicit formulas for A₃⊥, A₄⊥, A₅⊥.
7. A₃⊥ > 0 for all admissible parameters, hence d(C⊥) = 3.
8. When s is even, all primal weights are even, implying symmetry of C⊥.
-/
import Mathlib

/-! ## Section 1: Table 3 multiplicities -/

/-- Sum of Table 3 multiplicities equals 4q². -/
theorem sum_multiplicities (q s : ℤ) :
    1 + 2 + 1 + (q^2 - 1) + 2*(q+1-s)*(q-1) + (q+3-2*s)*(q-1) +
    2*s*(q-1) + (2*s-2)*(q-1) = 4 * q ^ 2 := by ring

/-! ## Section 2: Deriving m = 2t -/

theorem m_eq_2t (m t k : ℕ) (h : 2 ^ m + 3 * 2 ^ (2 * t) = 2 ^ k) : m = 2 * t := by
  by_contra h_neq; rcases lt_or_gt_of_ne h_neq with H|H <;> by_cases h : k-m > 0 <;> simp_all +decide ;
  · have h_factor : 2 ^ m + 3 * 2 ^ (2 * t) = 2 ^ m * (1 + 3 * 2 ^ (2 * t - m)) := by
      rw [ mul_add, mul_left_comm, ← pow_add, add_tsub_cancel_of_le H.le ] ; ring;
    have h_power : ∃ l : ℕ, 1 + 3 * 2 ^ (2 * t - m) = 2 ^ l := by
      exact ⟨ k - m, by rw [ ← mul_right_inj' ( pow_ne_zero _ two_ne_zero ), ← pow_add, Nat.add_sub_of_le h.le, ← h_factor, ‹2 ^ m + 3 * 2 ^ ( 2 * t ) = 2 ^ k› ] ⟩;
    rcases h_power with ⟨ l, hl ⟩ ; have := congr_arg Even hl ; norm_num [ Nat.even_add, Nat.even_mul, Nat.even_pow ] at this ; rcases l with ( _ | _ | l ) <;> simp_all +decide [ Nat.pow_succ' ] ;
    omega;
  · linarith [ pow_pos ( by decide : 0 < 2 ) m, pow_lt_pow_right₀ ( by decide : 1 < 2 ) H, pow_pos ( by decide : 0 < 2 ) ( 2 * t ), pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) h ] ;
  · have h_div : 2 ^ m ∣ 3 * 2 ^ (2 * t) := by
      exact ⟨ 2 ^ k / 2 ^ m - 1, by rw [ mul_tsub ] ; exact eq_tsub_of_add_eq <| by linarith [ Nat.div_mul_cancel <| show 2 ^ m ∣ 2 ^ k from pow_dvd_pow _ h.le ] ⟩;
    rw [ Nat.Prime.pow_dvd_iff_le_factorization ] at h_div <;> norm_num at * ; linarith;
  · linarith [ pow_pos ( by decide : 0 < 2 ) m, pow_pos ( by decide : 0 < 2 ) ( 2 * t ), pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) h ]

/-! ## Section 3: Power moments and A₁⊥ = A₂⊥ = 0 -/

/-- M₁ = 4h(2h−1), the first power moment from Table 3. -/
theorem M1_eq (q s h : ℤ) (hh : 2 * h = q ^ 2) :
    0 * 1 + s*(q-1) * 2 + (2*s-2)*(q-1) * 1 + h * (2*h - 1) +
    (h - s) * (2*(q+1-s)*(q-1)) + (h - (2*s-2)) * ((q+3-2*s)*(q-1)) +
    (h + q - s) * (2*s*(q-1)) + (h + q - (2*s-2)) * ((2*s-2)*(q-1))
    = 4 * h * (2 * h - 1) := by grind +ring

/-- M₂ = 4h²(2h−1), the second power moment from Table 3. -/
theorem M2_eq (q s h : ℤ) (hh : 2 * h = q ^ 2) :
    0^2 * 1 + (s*(q-1))^2 * 2 + ((2*s-2)*(q-1))^2 * 1 + h^2 * (2*h - 1) +
    (h - s)^2 * (2*(q+1-s)*(q-1)) + (h - (2*s-2))^2 * ((q+3-2*s)*(q-1)) +
    (h + q - s)^2 * (2*s*(q-1)) + (h + q - (2*s-2))^2 * ((2*s-2)*(q-1))
    = 4 * h ^ 2 * (2 * h - 1) := by grind +ring

/-- A₁⊥ = 0 from the first Pless power moment. -/
theorem A1_perp_zero {q : ℤ} (hq : q ≠ 0) {A1 : ℤ}
    (h : 2 * q^2 * (q^2 - 1 - A1) = 2 * q^2 * (q^2 - 1)) : A1 = 0 := by
  have hq2 : (q : ℤ) ^ 2 > 0 := by positivity
  nlinarith

/-- A₂⊥ = 0 from the second Pless power moment (using A₁⊥ = 0). -/
theorem A2_perp_zero {q : ℤ} (hq : q ≠ 0) {A2 : ℤ}
    (h : q^2 * ((q^2 - 1) * q^2 + 2 * A2) = q^4 * (q^2 - 1)) : A2 = 0 := by
  have hq2 : (q : ℤ) ^ 2 > 0 := by positivity
  nlinarith

/-! ## Section 4: Explicit dual weight formulas

The Krawtchouk polynomials in the variable D = n − 2w (where n = q²−1) are:
  6·K₃(w) = D(D² − 3n + 2)
  24·K₄(w) = D⁴ − (6n−8)D² + 3n(n−2)
  120·K₅(w) = D⁵ − (10n−20)D³ + (15n²−50n+24)D

For each of the 8 table weights, D depends only on q and s:
  weight 0:              D = q²−1
  weight s(q−1):         D = (q−1)(q+1−2s)
  weight (2s−2)(q−1):    D = (q−1)(q−4s+5)
  weight h = q²/2:       D = −1
  weight h−s:            D = 2s−1
  weight h−(2s−2):       D = 4s−5
  weight h+q−s:          D = −(2q−2s+1)
  weight h+q−(2s−2):     D = −(2q−4s+5)

The key identity |C|·j!·Bⱼ = Σ Aᵢ·j!·Kⱼ(wᵢ) reduces to a polynomial
identity in q and s, provable by `ring`.
-/

/-- Numerator of 6·A₃⊥. -/
def A3_numer (q s : ℤ) : ℤ :=
  q^4 + (3 - 6*s)*q^3 + (18*s^2 - 26*s + 10)*q^2
  + (-20*s^3 + 48*s^2 - 40*s + 12)*q
  + (20*s^3 - 66*s^2 + 72*s - 26)

/-- Numerator of 24·A₄⊥. -/
def A4_numer (q s : ℤ) : ℤ :=
  q^6 - 8*q^5*s + 36*q^4*s^2 - 80*q^3*s^3 + 72*q^2*s^4
  + 4*q^5 - 40*q^4*s + 120*q^3*s^2 - 16*q^2*s^3 - 288*q*s^4
  + 13*q^4 - 56*q^3*s - 324*q^2*s^2 + 1104*q*s^3 + 216*s^4
  - 4*q^3 + 488*q^2*s - 1632*q*s^2 - 1008*s^3
  - 198*q^2 + 1056*q*s + 1800*s^2
  - 240*q - 1440*s + 424

/-- Numerator of 120·A₅⊥. -/
def A5_numer (q s : ℤ) : ℤ :=
  q^8 - 10*q^7*s + 60*q^6*s^2 - 200*q^5*s^3 + 360*q^4*s^4 - 272*q^3*s^5
  + 5*q^7 - 70*q^6*s + 360*q^5*s^2 - 680*q^4*s^3 - 160*q^3*s^4 + 1360*q^2*s^5
  + 20*q^6 - 220*q^5*s + 180*q^4*s^2 + 2560*q^3*s^3 - 4600*q^2*s^4 - 2720*q*s^5
  + 30*q^5 + 508*q^4*s - 4520*q^3*s^2 + 4400*q^2*s^3 + 14240*q*s^4 + 1632*s^5
  - 264*q^4 + 2672*q^3*s + 2560*q^2*s^2 - 30720*q*s^3 - 9840*s^4
  - 440*q^3 - 6080*q^2*s + 32800*q*s^2 + 24640*s^3
  + 2440*q^2 - 16960*q*s - 31440*s^2
  + 3360*q + 20160*s - 5152

/-- The A₃⊥ formula via the third Pless power moment. -/
theorem A3_formula_pless (q s h : ℤ) (hh : 2 * h = q ^ 2) :
    h * (2*h - 1)^2 * (2*h + 2) -
    (0^3 * 1 + (s*(q-1))^3 * 2 + ((2*s-2)*(q-1))^3 * 1 + h^3 * (2*h - 1) +
     (h - s)^3 * (2*(q+1-s)*(q-1)) + (h - (2*s-2))^3 * ((q+3-2*s)*(q-1)) +
     (h + q - s)^3 * (2*s*(q-1)) + (h + q - (2*s-2))^3 * ((2*s-2)*(q-1)))
    = h * A3_numer q s := by unfold A3_numer; grind +ring

/-- The A₃⊥ formula via Krawtchouk: Σ Aᵢ·Dᵢ³ = 4q²·A3_numer, Dᵢ = n−2wᵢ. -/
theorem A3_formula_correct (q s : ℤ) :
    (q^2-1)^3 * 1 + ((q-1)*(q+1-2*s))^3 * 2 + ((q-1)*(q-4*s+5))^3 * 1 +
    (-1)^3 * (q^2-1) + (2*s-1)^3 * (2*(q+1-s)*(q-1)) +
    (4*s-5)^3 * ((q+3-2*s)*(q-1)) +
    (-(2*q-2*s+1))^3 * (2*s*(q-1)) + (-(2*q-4*s+5))^3 * ((2*s-2)*(q-1))
    = 4*q^2 * A3_numer q s := by unfold A3_numer; ring

/-- The A₄⊥ formula: Σ Aᵢ·Dᵢ⁴ = 4q²·(A4_numer + n(3n−2)), n = q²−1. -/
theorem A4_formula_correct (q s : ℤ) :
    (q^2-1)^4 * 1 + ((q-1)*(q+1-2*s))^4 * 2 + ((q-1)*(q-4*s+5))^4 * 1 +
    1 * (q^2-1) + (2*s-1)^4 * (2*(q+1-s)*(q-1)) +
    (4*s-5)^4 * ((q+3-2*s)*(q-1)) +
    (2*q-2*s+1)^4 * (2*s*(q-1)) + (2*q-4*s+5)^4 * ((2*s-2)*(q-1))
    = 4*q^2 * (A4_numer q s + (q^2-1)*(3*q^2-5)) := by unfold A4_numer; ring

/-- The A₅⊥ formula: Σ Aᵢ·Dᵢ⁵ = 4q²·(A5_numer + (10q²−30)·A3_numer). -/
theorem A5_formula_correct (q s : ℤ) :
    (q^2-1)^5 * 1 + ((q-1)*(q+1-2*s))^5 * 2 + ((q-1)*(q-4*s+5))^5 * 1 +
    (-1) * (q^2-1) + (2*s-1)^5 * (2*(q+1-s)*(q-1)) +
    (4*s-5)^5 * ((q+3-2*s)*(q-1)) +
    (-(2*q-2*s+1))^5 * (2*s*(q-1)) + (-(2*q-4*s+5))^5 * ((2*s-2)*(q-1))
    = 4*q^2 * (A5_numer q s + (10*q^2-30) * A3_numer q s) := by
  unfold A5_numer A3_numer; ring

/-! ## Section 5: Positivity of A₃⊥ and d(C⊥) = 3 -/

/-- A₃⊥ > 0 for q ≥ 8, 2 ≤ s ≤ q/2 − 1, hence d(C⊥) = 3. -/
theorem A3_numer_pos (q s : ℤ) (hq : 8 ≤ q) (hs_lo : 2 ≤ s) (hs_hi : 2 * s ≤ q - 2) :
    0 < A3_numer q s := by
  unfold A3_numer
  obtain ⟨r, rfl, hr₁, _⟩ : ∃ r : ℤ, q = 2 * s + r ∧ 2 ≤ r ∧ r ≤ q - 4 :=
    ⟨q - 2 * s, by ring, by linarith, by linarith⟩
  nlinarith only [sq_nonneg (s - 2), sq_nonneg (r - 2), hs_lo, hr₁,
    mul_le_mul_of_nonneg_left hr₁ (sub_nonneg.mpr hs_lo)]

/-! ## Section 6: Symmetry for even s -/

/-- When s is even and q is even, all 7 nonzero weights are even. -/
theorem all_weights_even_when_s_even (q s h : ℤ) (hs : 2 ∣ s) (hq : 2 ∣ q)
    (_hh : 2 * h = q ^ 2) (hh_even : 2 ∣ h) :
    (2 ∣ s * (q - 1)) ∧ (2 ∣ (2*s - 2) * (q - 1)) ∧ (2 ∣ h) ∧
    (2 ∣ (h - s)) ∧ (2 ∣ (h - (2*s - 2))) ∧
    (2 ∣ (h + q - s)) ∧ (2 ∣ (h + q - (2*s - 2))) := by
  simp_all +decide [← even_iff_two_dvd, parity_simps]

/-- q²/2 is even when 4 ∣ q (holds for q = 2^t, t ≥ 2). -/
theorem half_q_sq_even (q h : ℤ) (hh : 2 * h = q ^ 2) (h4 : 4 ∣ q) : 2 ∣ h := by
  rcases h4 with ⟨k, rfl⟩; exact ⟨4 * k ^ 2, by linarith⟩

/-! ## Section 7: Audit notes

1. **"8 non-zero weights"**: FALSE. Table 3 has 7 nonzero weights.
   Corrected in merged_dual.tex.

2. **A₃⊥ > 0 via "dense projective set"**: UNSUPPORTED from table data alone.
   Correct proof: algebraic F(q,r) positivity (A3_numer_pos).

3. **A₃⊥, A₄⊥, A₅⊥ formulas**: All verified via Krawtchouk polynomial identities.

4. **Symmetry for even s**: Verified — all primal weights even implies
   1 ∈ C⊥ and hence A_j⊥ = A_{n−j}⊥.
-/
