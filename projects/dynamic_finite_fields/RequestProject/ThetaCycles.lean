import Mathlib
import RequestProject.ThetaMap
import RequestProject.ThetaProjective

/-!
# Cycle Criteria for θ(x) = x + x⁻¹

This file contains the next layer of formalization targets: exact criteria
for genuine affine 3-cycles and 4-cycles of the map θ(x) = x + x⁻¹.

## Status

The following theorems are **fully verified** (no sorry):

- `third_iterate_num`: numerator of θ³(x) − x is 3x⁶ + 9x⁴ + 6x² + 1
- `three_cycle_poly_iff`: genuine affine 3-cycles ↔ 3x⁶ + 9x⁴ + 6x² + 1 = 0
- `three_cycles_le_two`: at most 6 period-3 points (at most 2 cycles)
- `fourth_iterate_factored`: θ⁴(x) = x ↔ (2x²+1)(2x⁴+4x²+1)(x⁸+7x⁶+14x⁴+8x²+1) = 0
- `four_cycle_poly_iff`: genuine 4-cycles ↔ (2x⁴+4x²+1)(x⁸+...) = 0 (char ≠ 2, 5)
- `four_cycles_le_three`: at most 12 period-4 points
- `theta2_eq_x_iff`: θ²(x) = x ↔ 2x²+1 = 0
- Various helper lemmas (`theta_eq_div`, `theta_ne_zero_iff`, `theta2_eq_div`,
  `theta3_eq_div`, etc.)

The following are now **fully verified** (previously sorry):

- `three_cycle_existence_iff_mod36`: 3-cycle exists ↔ q ≡ 1 (mod 36)
  (The irreducible-quadratic case uses AdjoinRoot and Frobenius action.)
- `four_cycle_count_formula'` (in `ThetaFourCycleHelpers.lean`):
  N₄ = 𝟙[q≡1 mod 16] + 2·𝟙[q≡1 mod 60]

## Correction to original stubs

The original `four_cycle_poly_iff` was stated with only `ringChar K ≠ 2`.
This is **false** in characteristic 5: when 2x²+1 = 0 (a period-2 point),
the octic factor x⁸+7x⁶+14x⁴+8x²+1 evaluates to −5/16, which vanishes
in char 5. The corrected version adds `ringChar K ≠ 5`.

## Main obstacle

The *existence* criteria (3-cycles exist iff q ≡ 1 mod 36; the 4-cycle count
formula involving q mod 16 and q mod 60) require arguing about the splitting
of real cyclotomic polynomials m₃₆, m₁₆, m₆₀ over F_q via Frobenius.
Mathlib currently lacks sufficient infrastructure for this argument at the
level of finite fields.
-/

noncomputable section

open Finset Polynomial

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-! ## Helper: iterated theta -/

/-- The second iterate θ²(x) = θ(θ(x)), defined for x ≠ 0 and θ(x) ≠ 0. -/
def theta2 (x : K) : K := theta (theta x)

/-- The third iterate θ³(x), defined for suitable x. -/
def theta3 (x : K) : K := theta (theta (theta x))

/-- The fourth iterate θ⁴(x). -/
def theta4 (x : K) : K := theta (theta (theta (theta x)))

/-! ## Third iterate identity -/

/-
PROBLEM
**Third iterate numerator identity** (polynomial form).
For x ≠ 0, x² + 1 ≠ 0, and x⁴ + 3x² + 1 ≠ 0,
  θ³(x) − x = (3x⁶ + 9x⁴ + 6x² + 1) / (x(x² + 1)(x⁴ + 3x² + 1)).

The denominator conditions ensure all intermediate values are nonzero.
The key algebraic content is that the numerator 3x⁶ + 9x⁴ + 6x² + 1
and denominator x(x²+1)(x⁴+3x²+1) are coprime in ℤ[x].

Proof strategy: direct algebraic simplification of θ(θ(θ(x))) − x,
clearing denominators step by step using the hypothesis that each
intermediate denominator is nonzero.

PROVIDED SOLUTION
Unfold theta3, theta2, theta. We have theta x = x + x⁻¹. Then theta (theta x) = theta x + (theta x)⁻¹, and theta3 x = theta (theta (theta x)).

Key intermediate facts:
- theta x = (x^2 + 1) / x, which is nonzero since h1 : x^2 + 1 ≠ 0 and hx : x ≠ 0
- theta2 x = (x^4 + 3*x^2 + 1) / (x * (x^2 + 1)), which is nonzero since h2 : x^4 + 3*x^2 + 1 ≠ 0

Strategy: Show both sides equal the same thing after clearing denominators. Use `have` to establish that theta x ≠ 0 (from h1 and hx), then theta (theta x) ≠ 0 (from h2), then unfold everything and use field_simp + ring.

To show theta x ≠ 0: theta x = x + x⁻¹ = (x^2 + 1) / x. Since x ≠ 0 and x^2 + 1 ≠ 0, this is nonzero. Use `div_ne_zero h1 hx` or prove directly.

Then use field_simp [hx, h1, h2, ...] followed by ring to verify the polynomial identity.
-/
theorem third_iterate_num {x : K} (hx : x ≠ 0) (hq : ringChar K ≠ 3)
    (h1 : x ^ 2 + 1 ≠ 0) (h2 : x ^ 4 + 3 * x ^ 2 + 1 ≠ 0) :
    theta3 x - x =
      (3 * x ^ 6 + 9 * x ^ 4 + 6 * x ^ 2 + 1) /
      (x * (x ^ 2 + 1) * (x ^ 4 + 3 * x ^ 2 + 1)) := by
  simp +decide only [theta3, theta];
  field_simp [hx]
  ring_nf at *;
  grind

/-! ## Three-cycle polynomial criterion -/

/-
PROBLEM
**Three-cycle polynomial criterion**.
For x ≠ 0 in a field of characteristic ≠ 2, 3, with no intermediate
θ-value hitting 0, the following are equivalent:
  (i)  x lies on a genuine affine 3-cycle (period exactly 3);
  (ii) θ³(x) = x;
  (iii) 3x⁶ + 9x⁴ + 6x² + 1 = 0.

The implication (ii) → (i) uses that θ has no affine fixed point
(so period ≠ 1) and that a period-2 point would satisfy θ²(x) = x,
forcing θ(x) = x via θ³(x) = x, a contradiction.

The step (ii) ↔ (iii) follows from `third_iterate_num` and coprimality
of numerator and denominator.

PROVIDED SOLUTION
We show: (theta3 x = x ∧ theta2 x ≠ x ∧ theta x ≠ x) ↔ 3*x^6 + 9*x^4 + 6*x^2 + 1 = 0.

Forward direction: If theta3 x = x, then by third_iterate_num, (3*x^6 + 9*x^4 + 6*x^2 + 1) / (x*(x^2+1)*(x^4+3*x^2+1)) = 0. Since the denominator is nonzero (mul_ne_zero, mul_ne_zero hx h1, h2), we get the numerator = 0.

Backward direction: If 3*x^6 + 9*x^4 + 6*x^2 + 1 = 0, then by third_iterate_num, theta3 x - x = 0, so theta3 x = x.
For theta x ≠ x: use theta_no_affine_fixed_point.
For theta2 x ≠ x: if theta2 x = x, then theta(theta(x)) = x, and also theta(theta(theta(x))) = theta(x), so theta3(x) = theta(x). But theta3(x) = x, so theta(x) = x, contradicting theta_no_affine_fixed_point.

Wait, actually, let me be more careful. theta2 x ≠ x needs a separate argument.

If theta2 x = x and theta3 x = x, then theta3 x = theta(theta2 x) = theta(x). But theta3 x = x, so theta(x) = x, contradicting theta_no_affine_fixed_point.

So the key steps are:
1. Use third_iterate_num to convert between theta3 x = x and the polynomial equation
2. Use theta_no_affine_fixed_point to show theta x ≠ x always
3. Show theta2 x ≠ x follows from theta3 x = x and theta x ≠ x: if theta2 x = x then theta3 x = theta(theta2 x) = theta(x), so theta3 x = x gives theta(x) = x, contradiction.
-/
theorem three_cycle_poly_iff {x : K} (hx : x ≠ 0)
    (hchar2 : ringChar K ≠ 2) (hchar3 : ringChar K ≠ 3)
    (h1 : x ^ 2 + 1 ≠ 0) (h2 : x ^ 4 + 3 * x ^ 2 + 1 ≠ 0) :
    (theta3 x = x ∧ theta2 x ≠ x ∧ theta x ≠ x) ↔
    3 * x ^ 6 + 9 * x ^ 4 + 6 * x ^ 2 + 1 = 0 := by
  constructor <;> intro h3 <;> simp_all +decide [ theta3, theta2, theta ];
  · field_simp at *;
    have := h3.1;
    rw [ div_eq_iff ] at this <;> ring_nf at * <;> simp_all +decide [ add_eq_zero_iff_eq_neg ];
    linear_combination' this;
  · have h_inv : (3 * x ^ 6 + 9 * x ^ 4 + 6 * x ^ 2 + 1) / (x * (x ^ 2 + 1) * (x ^ 4 + 3 * x ^ 2 + 1)) = 0 := by
      rw [ h3, zero_div ];
    have h_inv : (x + x⁻¹ + (x + x⁻¹)⁻¹ + (x + x⁻¹ + (x + x⁻¹)⁻¹)⁻¹) - x = 0 := by
      convert h_inv using 1;
      convert third_iterate_num hx hchar3 h1 h2 using 1;
    grind

/-
PROBLEM
**At most two affine 3-cycles**.
In odd characteristic ≠ 3, the polynomial 3x⁶ + 9x⁴ + 6x² + 1 has
at most 6 roots in K (degree 6), so there are at most two genuine affine 3-cycles.

PROVIDED SOLUTION
We need to show the set of x with x ≠ 0, theta3 x = x, theta2 x ≠ x, theta x ≠ x has cardinality ≤ 6.

Approach: Show this set is a subset of the roots of the polynomial 3*X^6 + 9*X^4 + 6*X^2 + 1 in K[X]. Since this polynomial has degree 6, it has at most 6 roots.

More precisely:
1. Every element in the filtered set satisfies 3*x^6 + 9*x^4 + 6*x^2 + 1 = 0 (by three_cycle_poly_iff, under appropriate conditions).
2. But we need to be careful: three_cycle_poly_iff requires h1: x^2+1≠0 and h2: x^4+3x^2+1≠0.

Alternative simpler approach: Show that every x in the set satisfies theta3 x = x, which means theta(theta(theta(x))) = x. Unfold and show this implies a polynomial equation of degree ≤ 6 or ≤ 7 (possibly after clearing denominators). Then use the fact that a polynomial of degree d has at most d roots.

Actually, let me think more carefully. The set S = {x : x ≠ 0 ∧ theta3 x = x ∧ theta2 x ≠ x ∧ theta x ≠ x}. We want |S| ≤ 6.

Key insight: Every element x in S satisfies theta3 x = x, which means x is a root of the equation theta(theta(theta(t))) = t. This equation, after clearing denominators, gives a polynomial equation. The polynomial 3t^6 + 9t^4 + 6t^2 + 1 is the numerator of θ³(t) - t (after clearing denominators), so elements of S are among the roots of this degree-6 polynomial. Hence |S| ≤ 6.

But to use three_cycle_poly_iff directly, we need the hypotheses h1 and h2. Let me check:
- If x^2 + 1 = 0, then theta(x) = 0, so theta2(x) = theta(0) = 0, theta3(x) = 0. theta3(x) = x implies x = 0, contradicting x ≠ 0. So x^2 + 1 ≠ 0 for any x in S.
- If x^4 + 3x^2 + 1 = 0, then theta2(x) = 0, theta3(x) = 0, so theta3(x) = x implies x = 0, contradiction. So x^4 + 3x^2 + 1 ≠ 0 for any x in S.

So actually the approach works: embed S into the roots of the polynomial p = 3*X^6 + 9*X^4 + 6*X^2 + 1 ∈ K[X], which has degree ≤ 6, giving |S| ≤ 6.

Technically, we need to check that this polynomial is nonzero (to apply degree bound). In characteristic ≠ 3, the leading coefficient 3 ≠ 0, so natDegree = 6. Actually we also need char ≠ 3, which is given.

Use Finset.card_le_card to bound the cardinality by the number of roots of the polynomial, then use Polynomial.card_roots_le_degree or Multiset.card_le_card with Polynomial.roots.
-/
theorem three_cycles_le_two (hchar2 : ringChar K ≠ 2) (hchar3 : ringChar K ≠ 3) :
    (Finset.univ.filter (fun x : K =>
      x ≠ 0 ∧ theta3 x = x ∧ theta2 x ≠ x ∧ theta x ≠ x)).card ≤ 6 := by
  -- Let's define the polynomial $P(x) = 3x^6 + 9x^4 + 6x^2 + 1$.
  set P : Polynomial K := Polynomial.C 3 * Polynomial.X ^ 6 + Polynomial.C 9 * Polynomial.X ^ 4 + Polynomial.C 6 * Polynomial.X ^ 2 + Polynomial.C 1;
  -- By definition of $P$, we know that every element $x$ in the set satisfies $P(x) = 0$.
  have hP : ∀ x : K, x ≠ 0 ∧ theta3 x = x ∧ theta2 x ≠ x ∧ theta x ≠ x → P.eval x = 0 := by
    intro x hx; by_cases h1 : x ^ 2 + 1 = 0 <;> by_cases h2 : x ^ 4 + 3 * x ^ 2 + 1 = 0 <;> simp_all +decide [ Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C ] ;
    · grind +ring;
    · unfold theta3 theta2 at hx ; simp_all +decide [ pow_succ, mul_assoc, add_eq_zero_iff_eq_neg ];
      grind;
    · unfold theta3 at hx; simp_all +decide [ theta ] ;
      grind;
    · have := three_cycle_poly_iff hx.1 hchar2 hchar3 h1 h2; aesop;
  refine' le_trans ( Finset.card_le_card _ ) ( le_trans ( Multiset.toFinset_card_le _ ) _ );
  case refine'_2 => exact P.roots;
  · simp_all +decide [ Finset.subset_iff ];
    intro x hx hx' hx''; intro H; have := congr_arg ( Polynomial.eval 0 ) H; norm_num at this;
    simp +zetaDelta at *;
  · refine' le_trans ( Polynomial.card_roots' P ) _;
    rw [ Polynomial.natDegree_le_iff_degree_le, Polynomial.degree_le_iff_coeff_zero ];
    aesop

/-! ## Fourth iterate identity: helper lemmas -/

/-
PROBLEM
theta x expressed as a fraction

PROVIDED SOLUTION
theta x = x + x⁻¹ = (x² + 1) / x. Use field_simp and ring.
-/
lemma theta_eq_div {x : K} (hx : x ≠ 0) : theta x = (x ^ 2 + 1) / x := by
  simp +decide [ theta, hx, sq, add_div ]

/-
PROBLEM
theta x is nonzero iff x^2 + 1 ≠ 0

PROVIDED SOLUTION
theta x = (x² + 1) / x by theta_eq_div. So theta x ≠ 0 iff (x²+1)/x ≠ 0 iff x²+1 ≠ 0 (since x ≠ 0). Use div_ne_zero_iff or similar.
-/
lemma theta_ne_zero_iff {x : K} (hx : x ≠ 0) : theta x ≠ 0 ↔ x ^ 2 + 1 ≠ 0 := by
  simp +decide [ add_eq_zero_iff_eq_neg, hx, inv_eq_zero, theta ];
  grind

/-
PROBLEM
theta2 expressed as a fraction when theta x ≠ 0

PROVIDED SOLUTION
theta2 x = theta(theta x) = theta((x²+1)/x). Since (x²+1)/x ≠ 0 (by h1 and hx), we have theta((x²+1)/x) = ((x²+1)/x)² + 1) / ((x²+1)/x) = ((x²+1)² + x²) / (x(x²+1)) = (x⁴+3x²+1)/(x(x²+1)). Use theta_eq_div, field_simp, ring.
-/
lemma theta2_eq_div {x : K} (hx : x ≠ 0) (h1 : x ^ 2 + 1 ≠ 0) :
    theta2 x = (x ^ 4 + 3 * x ^ 2 + 1) / (x * (x ^ 2 + 1)) := by
  unfold theta2 theta
  field_simp [hx, h1]
  ring

/-
PROBLEM
theta3 expressed as a fraction

PROVIDED SOLUTION
Similar to theta2_eq_div. Unfold theta3 theta, then field_simp [hx, h1, h2], then ring.
-/
lemma theta3_eq_div {x : K} (hx : x ≠ 0) (h1 : x ^ 2 + 1 ≠ 0) (h2 : x ^ 4 + 3 * x ^ 2 + 1 ≠ 0) :
    theta3 x = (x ^ 8 + 7 * x ^ 6 + 13 * x ^ 4 + 7 * x ^ 2 + 1) /
      (x * (x ^ 2 + 1) * (x ^ 4 + 3 * x ^ 2 + 1)) := by
  convert theta2_eq_div _ _ using 1;
  · rw [ show theta x = ( x ^ 2 + 1 ) / x from ?_ ];
    · field_simp [hx, h1, h2]
      ring;
    · exact theta_eq_div hx;
  · infer_instance;
  · infer_instance;
  · exact (theta_ne_zero_iff hx).mpr h1;
  · simp_all +decide [ theta ];
    grind +ring

/-- theta x = 0 implies theta2 x = 0 -/
lemma theta_zero_imp_theta2_zero {x : K} (h : theta x = 0) : theta2 x = 0 := by
  show theta (theta x) = 0; rw [h]; simp [theta]

/-- theta2 x = 0 implies theta3 x = 0 -/
lemma theta2_zero_imp_theta3_zero {x : K} (h : theta2 x = 0) : theta3 x = 0 := by
  show theta (theta (theta x)) = 0
  have : theta (theta x) = 0 := h
  rw [this]; simp [theta]

/-- theta3 x = 0 implies theta4 x = 0 -/
lemma theta3_zero_imp_theta4_zero {x : K} (h : theta3 x = 0) : theta4 x = 0 := by
  show theta (theta (theta (theta x))) = 0
  have : theta (theta (theta x)) = 0 := h
  rw [this]; simp [theta]

/-
PROBLEM
When x^2 + 1 = 0, the product (2x^2+1)(2x^4+4x^2+1)(x^8+...) ≠ 0

PROVIDED SOLUTION
We have x² = -1 (from h : x²+1 = 0). Then:
- 2x²+1 = 2(-1)+1 = -1
- x⁴ = (x²)² = 1, so 2x⁴+4x²+1 = 2-4+1 = -1
- x⁸ = 1, x⁶ = x⁴·x² = -1, so x⁸+7x⁶+14x⁴+8x²+1 = 1-7+14-8+1 = 1
Product = (-1)(-1)(1) = 1. Since char ≠ 2, 1 ≠ 0.

Approach: substitute x²=-1 everywhere using have h' : x^2 = -1 := by linarith, then simplify using ring_nf and show the product equals 1. Then use one_ne_zero.
-/
lemma fourth_rhs_ne_zero_of_sq_neg_one {x : K} (h : x ^ 2 + 1 = 0)
    (hchar2 : ringChar K ≠ 2) :
    (2 * x ^ 2 + 1) * (2 * x ^ 4 + 4 * x ^ 2 + 1) *
    (x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1) ≠ 0 := by
  simp_all +decide [ show x ^ 4 = x ^ 2 * x ^ 2 by ring, show x ^ 6 = x ^ 4 * x ^ 2 by ring, show x ^ 8 = x ^ 6 * x ^ 2 by ring ];
  simp_all +decide [ show x ^ 2 = -1 by linear_combination' h ] ; ring_nf at * ; aesop;

/-
PROBLEM
When x^4 + 3x^2 + 1 = 0, the product ≠ 0

PROVIDED SOLUTION
We have x⁴+3x²+1 = 0, x²+1 ≠ 0, x ≠ 0, char ≠ 2. We need to show the product (2x²+1)(2x⁴+4x²+1)(x⁸+7x⁶+14x⁴+8x²+1) ≠ 0.

From x⁴ = -3x²-1:
- 2x⁴+4x²+1 = 2(-3x²-1)+4x²+1 = -2x²-1 = -(2x²+1)
- x⁸ = (x⁴)² = (3x²+1)² = 9x⁴+6x²+1 = 9(-3x²-1)+6x²+1 = -21x²-8
- 7x⁶ = 7x²·x⁴ = 7x²(-3x²-1) = -21x⁴-7x² = -21(-3x²-1)-7x² = 56x²+21
- 14x⁴ = 14(-3x²-1) = -42x²-14
- x⁸+7x⁶+14x⁴+8x²+1 = (-21x²-8)+(56x²+21)+(-42x²-14)+8x²+1 = x²
So the product = (2x²+1)(-(2x²+1))(x²) = -(2x²+1)²·x².

This is zero iff x = 0 or 2x²+1 = 0.
x ≠ 0 by hypothesis.
If 2x²+1 = 0, then x² = -1/2, x⁴ = 1/4. But x⁴+3x²+1 = 1/4-3/2+1 = -1/4 ≠ 0, contradicting h.
So the product ≠ 0.

Alternative: show the product equals -(2x²+1)²·x² using ring-like reasoning modulo x⁴+3x²+1 = 0, then show this is nonzero by contradiction.
-/
lemma fourth_rhs_ne_zero_of_quartic_zero {x : K} (hx : x ≠ 0)
    (h1 : x ^ 2 + 1 ≠ 0) (h : x ^ 4 + 3 * x ^ 2 + 1 = 0)
    (hchar2 : ringChar K ≠ 2) :
    (2 * x ^ 2 + 1) * (2 * x ^ 4 + 4 * x ^ 2 + 1) *
    (x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1) ≠ 0 := by
  grind

/-
PROBLEM
When x^8 + 7x^6 + 13x^4 + 7x^2 + 1 = 0, the product ≠ 0

PROVIDED SOLUTION
We have x⁸+7x⁶+13x⁴+7x²+1 = 0, x²+1 ≠ 0, x⁴+3x²+1 ≠ 0, x ≠ 0, char ≠ 2.

Key: x⁸+7x⁶+14x⁴+8x²+1 = (x⁸+7x⁶+13x⁴+7x²+1) + (x⁴+x²) = x⁴+x² = x²(x²+1).

So the product = (2x²+1)(2x⁴+4x²+1)·x²(x²+1).

This is nonzero since x ≠ 0 (so x² ≠ 0), x²+1 ≠ 0, and we need 2x²+1 ≠ 0 and 2x⁴+4x²+1 ≠ 0.

For 2x²+1 ≠ 0: if 2x²+1 = 0 then x² = -1/2, x⁴ = 1/4. Compute x⁸+7x⁶+13x⁴+7x²+1 with these values. x⁸ = 1/16, x⁶ = -1/8. So 1/16 - 7/8 + 13/4 - 7/2 + 1 = (1-14+52-56+16)/16 = -1/16 ≠ 0. Contradiction.

For 2x⁴+4x²+1 ≠ 0: if 2x⁴+4x²+1 = 0 then x⁴ = -(4x²+1)/2. Use this in x⁸+7x⁶+13x⁴+7x²+1 = 0 to derive a contradiction. x⁸ = x⁴·x⁴ = ((4x²+1)/2)² = (16x⁴+8x²+1)/4 = (16·(-(4x²+1)/2)+8x²+1)/4 = (-32x²-8+8x²+1)/4 = (-24x²-7)/4. And x⁶ = x²·x⁴ = x²·(-(4x²+1)/2) = -(4x⁴+x²)/2 = -(4·(-(4x²+1)/2)+x²)/2 = -(-8x²-2+x²)/2 = (7x²+2)/2. Then x⁸+7x⁶+13x⁴+7x²+1 = (-24x²-7)/4 + 7(7x²+2)/2 + 13·(-(4x²+1)/2) + 7x² + 1 = (-24x²-7)/4 + (49x²+14)/2 + (-52x²-13)/2 + 7x² + 1 = (-24x²-7)/4 + (-3x²+1)/2 + 7x² + 1 = (-24x²-7 - 6x²+2)/4 + 7x² + 1 = (-30x²-5)/4 + 7x² + 1 = (-30x²-5+28x²+4)/4 = (-2x²-1)/4 = -(2x²+1)/4. If 2x⁴+4x²+1=0 then x⁸+...+1 = -(2x²+1)/4 = 0 iff 2x²+1=0. But if both 2x²+1=0 and 2x⁴+4x²+1=0, then x²=-1/2, x⁴=1/4, and 2(1/4)+4(-1/2)+1 = 1/2-2+1 = -1/2 ≠ 0. Contradiction.

So the product ≠ 0.

Use intro habs, then mul_eq_zero to decompose, handle each factor being zero by deriving contradictions using the above calculations.
-/
lemma fourth_rhs_ne_zero_of_octic_zero {x : K} (hx : x ≠ 0)
    (h1 : x ^ 2 + 1 ≠ 0) (h2 : x ^ 4 + 3 * x ^ 2 + 1 ≠ 0)
    (h : x ^ 8 + 7 * x ^ 6 + 13 * x ^ 4 + 7 * x ^ 2 + 1 = 0)
    (hchar2 : ringChar K ≠ 2) :
    (2 * x ^ 2 + 1) * (2 * x ^ 4 + 4 * x ^ 2 + 1) *
    (x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1) ≠ 0 := by
  simp +decide +zetaDelta (disch := grind) at *;
  refine' ⟨ ⟨ _, _ ⟩, _ ⟩;
  · grind +ring;
  · contrapose! h1;
    grind +ring;
  · intro H; simp_all +decide [ show x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1 = ( x ^ 8 + 7 * x ^ 6 + 13 * x ^ 4 + 7 * x ^ 2 + 1 ) + ( x ^ 4 + x ^ 2 ) by ring ] ;
    grind

/-
PROBLEM
**Fourth iterate identity** (generic case, all denominators nonzero).
θ⁴(x) = x iff the product of three factors vanishes.

PROVIDED SOLUTION
We have all denominators nonzero: x ≠ 0, x²+1 ≠ 0, x⁴+3x²+1 ≠ 0, x⁸+7x⁶+13x⁴+7x²+1 ≠ 0.

Strategy: Unfold theta4 and theta, use field_simp with all the nonzero conditions, then ring.

Specifically: theta4 x = theta(theta(theta(theta x))). Each theta(y) = y + y⁻¹. We need field_simp to handle all 4 levels of inversion.

Key intermediate nonzero conditions (for field_simp):
- x ≠ 0 (given)
- theta x = (x²+1)/x ≠ 0 (from h1)
- theta2 x = (x⁴+3x²+1)/(x(x²+1)) ≠ 0 (from h2)
- theta3 x = (x⁸+7x⁶+13x⁴+7x²+1)/(x(x²+1)(x⁴+3x²+1)) ≠ 0 (from h3)

Establish these with `have` statements, then unfold theta4 theta, field_simp, ring.

Use set_option maxHeartbeats high (e.g., 6400000 or higher).
-/
lemma fourth_iterate_factored_generic {x : K} (hx : x ≠ 0)
    (hchar2 : ringChar K ≠ 2)
    (h1 : x ^ 2 + 1 ≠ 0)
    (h2 : x ^ 4 + 3 * x ^ 2 + 1 ≠ 0)
    (h3 : x ^ 8 + 7 * x ^ 6 + 13 * x ^ 4 + 7 * x ^ 2 + 1 ≠ 0) :
    theta4 x = x ↔
    (2 * x ^ 2 + 1) * (2 * x ^ 4 + 4 * x ^ 2 + 1) *
    (x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1) = 0 := by
  unfold theta4 theta;
  have h_denom_nonzero : x * (x + x⁻¹) * (x + x⁻¹ + (x + x⁻¹)⁻¹) * (x + x⁻¹ + (x + x⁻¹)⁻¹ + (x + x⁻¹ + (x + x⁻¹)⁻¹)⁻¹) ≠ 0 := by
    simp_all +decide [ add_eq_zero_iff_eq_neg, mul_assoc ];
    grind;
  -- Since the denominators are non-zero, we can multiply both sides of the equation by the product of the denominators to eliminate the fractions.
  field_simp [h_denom_nonzero] at *;
  rw [ div_eq_iff ];
  · exact ⟨ fun h => by linear_combination' h, fun h => by linear_combination' h ⟩;
  · aesop

/-! ## Fourth iterate identity -/

/-- **Fourth iterate factorization**.
The numerator of θ⁴(x) − x factors (over ℤ[x]) as
  (2x² + 1) · (2x⁴ + 4x² + 1) · (x⁸ + 7x⁶ + 14x⁴ + 8x² + 1).
The first factor (2x² + 1) cuts out the affine period-2 points (x² = −1/2).
The remaining two factors are the "exact period-4" polynomial. -/
theorem fourth_iterate_factored {x : K} (hx : x ≠ 0)
    (hchar2 : ringChar K ≠ 2) :
    theta4 x = x ↔
    (2 * x ^ 2 + 1) * (2 * x ^ 4 + 4 * x ^ 2 + 1) *
    (x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1) = 0 := by
  by_cases h1 : x ^ 2 + 1 = 0
  · -- theta x = 0, so theta4 x = 0 ≠ x, and RHS ≠ 0
    constructor
    · intro h4
      have : theta x = 0 := by rw [theta_eq_div hx]; simp [h1]
      have h4zero : theta4 x = 0 := theta3_zero_imp_theta4_zero (theta2_zero_imp_theta3_zero (theta_zero_imp_theta2_zero this))
      rw [h4zero] at h4; exact absurd h4.symm hx
    · intro hprod; exact absurd hprod (fourth_rhs_ne_zero_of_sq_neg_one h1 hchar2)
  · by_cases h2 : x ^ 4 + 3 * x ^ 2 + 1 = 0
    · constructor
      · intro h4
        have : theta2 x = 0 := by rw [theta2_eq_div hx h1]; simp [h2]
        have h4zero : theta4 x = 0 := theta3_zero_imp_theta4_zero (theta2_zero_imp_theta3_zero this)
        rw [h4zero] at h4; exact absurd h4.symm hx
      · intro hprod; exact absurd hprod (fourth_rhs_ne_zero_of_quartic_zero hx h1 h2 hchar2)
    · by_cases h3 : x ^ 8 + 7 * x ^ 6 + 13 * x ^ 4 + 7 * x ^ 2 + 1 = 0
      · constructor
        · intro h4
          -- theta3 x = 0 when the octic vanishes
          have htheta_ne : theta x ≠ 0 := (theta_ne_zero_iff hx).mpr h1
          have htheta2_ne : theta2 x ≠ 0 := by
            rw [theta2_eq_div hx h1]
            exact div_ne_zero (by exact_mod_cast h2) (mul_ne_zero hx h1)
          have : theta3 x = 0 := by rw [theta3_eq_div hx h1 h2]; simp [h3]
          have h4zero : theta4 x = 0 := theta3_zero_imp_theta4_zero this
          rw [h4zero] at h4; exact absurd h4.symm hx
        · intro hprod; exact absurd hprod (fourth_rhs_ne_zero_of_octic_zero hx h1 h2 h3 hchar2)
      · exact fourth_iterate_factored_generic hx hchar2 h1 h2 h3

/-
PROBLEM
In char ≠ 2, x ≠ 0: θ²(x) = x ↔ 2x²+1 = 0.

If x²+1 = 0 then θ(x) = 0, θ²(x) = 0 ≠ x. So θ²(x) = x requires x²+1 ≠ 0,
hence θ(x) ≠ 0. By `two_cycle_poly`, (2x²+1)(x²+1) = 0, giving 2x²+1 = 0.
Converse: direct computation.

PROVIDED SOLUTION
Forward: theta2 x = x. First check if theta x = 0 (i.e., x²+1=0). If so, theta2 x = 0 ≠ x (x≠0), contradiction. So theta x ≠ 0. Then by two_cycle_poly, (2x²+1)(x²+1) = 0. Since x²+1 ≠ 0 (as theta x ≠ 0 requires x²+1 ≠ 0 by theta_ne_zero_iff), we get 2x²+1 = 0.

Backward: 2x²+1 = 0 means x² = -1/2. Compute theta x = (x²+1)/x = (1/2)/x = 1/(2x). Then theta2 x = theta(1/(2x)) = 1/(2x) + 2x = (1+4x²)/(2x) = (1-2)/(2x) = -1/(2x). And -1/(2x) = x iff -1 = 2x² iff 2x²+1 = 0. So theta2 x = x. ✓

Use unfold theta2 theta, field_simp, and handle both directions.
-/
lemma theta2_eq_x_iff {x : K} (hx : x ≠ 0) (hchar2 : ringChar K ≠ 2) :
    theta2 x = x ↔ 2 * x ^ 2 + 1 = 0 := by
  unfold theta2;
  unfold theta;
  grind

/-
PROBLEM
The original statement of `four_cycle_poly_iff` without a `ringChar K ≠ 5`
hypothesis is **false** in characteristic 5: when 2x²+1 = 0 (a period-2 point),
the octic factor x⁸+7x⁶+14x⁴+8x²+1 evaluates to −5/16, which vanishes
in char 5, making the RHS true while the LHS is false (theta2 x = x).
The corrected version below adds `ringChar K ≠ 5`.

**Four-cycle polynomial criterion** (corrected: requires char ≠ 2, 5).
x lies on a genuine affine 4-cycle if and only if
  (2x⁴ + 4x² + 1)(x⁸ + 7x⁶ + 14x⁴ + 8x² + 1) = 0.
The factor 2x²+1 is excluded because those are exactly the affine period-2
points (θ²(x) = x). The separation of period-2 and period-4 roots requires
char ≠ 5 because the resultant of 2x²+1 and x⁸+7x⁶+14x⁴+8x²+1 is 5/32.

PROVIDED SOLUTION
We need: (theta4 x = x ∧ theta2 x ≠ x) ↔ (2x⁴+4x²+1)(x⁸+7x⁶+14x⁴+8x²+1) = 0.

Forward (→): theta4 x = x, so by fourth_iterate_factored, (2x²+1)(2x⁴+4x²+1)(x⁸+...) = 0. Since theta2 x ≠ x, by theta2_eq_x_iff we have 2x²+1 ≠ 0. So (2x⁴+4x²+1)(x⁸+...) = 0.

Backward (←): If (2x⁴+4x²+1)(x⁸+...) = 0, then (2x²+1)·(2x⁴+4x²+1)·(x⁸+...) = 0 (multiply by anything). So by fourth_iterate_factored, theta4 x = x.

For theta2 x ≠ x: by contrapositive, if theta2 x = x then by theta2_eq_x_iff, 2x²+1 = 0, i.e., x² = -1/2. Then evaluate (2x⁴+4x²+1)(x⁸+7x⁶+14x⁴+8x²+1) at x² = -1/2 to get (-1/2)(-5/16) = 5/32. Since char ≠ 2 and char ≠ 5, we need 5 ≠ 0 in K. Use hchar5 to show (5:K) ≠ 0, hence 5/32 ≠ 0, contradicting the assumption that the product = 0.

The key step for showing 5 ≠ 0: if (5:K) = 0 then ringChar K | 5, and since ringChar K is 0 or prime, ringChar K = 5, contradicting hchar5.
-/
theorem four_cycle_poly_iff {x : K} (hx : x ≠ 0)
    (hchar2 : ringChar K ≠ 2) (hchar5 : ringChar K ≠ 5) :
    (theta4 x = x ∧ theta2 x ≠ x) ↔
    (2 * x ^ 4 + 4 * x ^ 2 + 1) * (x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1) = 0 := by
  constructor <;> intro h;
  · have := fourth_iterate_factored hx hchar2;
    have := theta2_eq_x_iff hx hchar2; aesop;
  · -- By the fourth_iterate_factored lemma, we have theta4 x = x.
    have h_theta4 : theta4 x = x := by
      exact ( fourth_iterate_factored hx hchar2 ) |>.2 ( by linear_combination' h * ( 2 * x ^ 2 + 1 ) );
    refine' ⟨ h_theta4, _ ⟩;
    intro h_eq
    have h_char5 : (5 : K) = 0 := by
      have h_char5 : x ^ 2 = -1 / 2 := by
        have h_char5 : 2 * x ^ 2 + 1 = 0 := by
          exact (theta2_eq_x_iff hx hchar2).mp h_eq;
        exact eq_div_of_mul_eq ( by aesop ) ( by linear_combination' h_char5 );
      grind;
    have := ringChar.spec K 5; simp_all +decide ;
    have := Nat.le_of_dvd ( by decide ) this; interval_cases _ : ringChar K <;> simp_all +decide ;
    exact absurd ( ‹Subsingleton K›.elim 0 1 ) ( by simp +decide )

/-
PROBLEM
**At most three genuine affine 4-cycles**.
The exact-period-4 polynomial has degree 4 + 8 = 12, giving at most 12 period-4 points,
hence at most 3 affine 4-cycles.

PROVIDED SOLUTION
We need: |{x ≠ 0 : theta4 x = x ∧ theta2 x ≠ x}| ≤ 12.

Strategy: Embed the set into roots of the degree-12 polynomial Q(x) = (2x⁴+4x²+1)(x⁸+7x⁶+14x⁴+8x²+1).

For any x in the set:
1. theta4 x = x, so by fourth_iterate_factored (needs char ≠ 2), (2x²+1)(2x⁴+4x²+1)(x⁸+...) = 0.
2. theta2 x ≠ x, so by theta2_eq_x_iff (needs char ≠ 2), 2x²+1 ≠ 0.
3. Therefore Q(x) = (2x⁴+4x²+1)(x⁸+...) = 0.

So the set embeds into the roots of Q, which has degree 4+8 = 12. A nonzero polynomial of degree ≤ 12 has at most 12 roots in K.

For Q to be nonzero: the leading term of Q over ℤ is 2x¹². In char ≠ 2, this is nonzero, so Q is a nonzero polynomial of degree 12.

Use Finset.card_le_card to bound the cardinality, embed into roots of Q via Polynomial.roots, and use Polynomial.card_roots_le_degree.
-/
theorem four_cycles_le_three (hchar2 : ringChar K ≠ 2) :
    (Finset.univ.filter (fun x : K =>
      x ≠ 0 ∧ theta4 x = x ∧ theta2 x ≠ x)).card ≤ 12 := by
  -- Let's denote the polynomial $Q(x)$ as $(2x^4 + 4x^2 + 1)(x^8 + 7x^6 + 14x^4 + 8x^2 + 1)$.
  set Q : Polynomial K := (2 * Polynomial.X ^ 4 + 4 * Polynomial.X ^ 2 + 1) * (Polynomial.X ^ 8 + 7 * Polynomial.X ^ 6 + 14 * Polynomial.X ^ 4 + 8 * Polynomial.X ^ 2 + 1);
  -- By definition of $Q$, we know that every element $x$ in the set satisfies $Q(x) = 0$.
  have hQ_roots : ∀ x : K, x ≠ 0 ∧ theta4 x = x ∧ theta2 x ≠ x → Q.eval x = 0 := by
    intro x hx
    have hQ : (2 * x ^ 2 + 1) * (2 * x ^ 4 + 4 * x ^ 2 + 1) * (x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1) = 0 := by
      exact fourth_iterate_factored hx.1 hchar2 |>.1 hx.2.1 |> fun h => by linear_combination' h;
    simp +zetaDelta at *;
    contrapose! hx; simp_all +decide [ theta2_eq_x_iff ] ;
  -- Since $Q$ is a polynomial of degree 12, it can have at most 12 roots in $K$.
  have hQ_deg : Q.degree ≤ 12 := by
    erw [ Polynomial.degree_le_iff_coeff_zero ];
    simp +zetaDelta at *;
    intro m hm; rcases m with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | m ) <;> simp_all +decide [ mul_assoc, add_mul, Polynomial.coeff_eq_zero_of_natDegree_lt ] ;
  refine' le_trans _ ( Polynomial.card_roots' Q ) |> le_trans <| Polynomial.natDegree_le_of_degree_le hQ_deg |> fun h => h.trans <| by norm_num;
  exact le_trans ( Finset.card_le_card <| show Finset.filter ( fun x : K => x ≠ 0 ∧ theta4 x = x ∧ theta2 x ≠ x ) Finset.univ ⊆ Q.roots.toFinset from fun x hx => Multiset.mem_toFinset.mpr <| Polynomial.mem_roots ( show Q ≠ 0 from by
                                                                                                                                                                                                                        simp +zetaDelta at *;
                                                                                                                                                                                                                        exact ⟨ ne_of_apply_ne ( Polynomial.eval 0 ) ( by simp +decide ), ne_of_apply_ne ( Polynomial.eval 0 ) ( by simp +decide ) ⟩ ) |>.2 <| hQ_roots x <| Finset.mem_filter.mp hx |>.2 ) <| Multiset.toFinset_card_le _

/-! ## Imaginary unit power reductions

These helper lemmas reduce powers of i (with i² = −1) to ±1,
used in the substitution bridge lemmas below. -/

/-- i⁴ = 1 when i² = −1. -/
lemma sq_neg_one_pow_four {i : K} (hi : i ^ 2 = -1) : i ^ 4 = 1 := by
  have : i ^ 4 = (i ^ 2) ^ 2 := by ring
  rw [this, hi]; ring

/-- i⁶ = −1 when i² = −1. -/
lemma sq_neg_one_pow_six {i : K} (hi : i ^ 2 = -1) : i ^ 6 = -1 := by
  have : i ^ 6 = (i ^ 2) ^ 3 := by ring
  rw [this, hi]; ring

/-- i⁸ = 1 when i² = −1. -/
lemma sq_neg_one_pow_eight {i : K} (hi : i ^ 2 = -1) : i ^ 8 = 1 := by
  have : i ^ 8 = (i ^ 2) ^ 4 := by ring
  rw [this, hi]; ring

/-! ## Algebraic substitution bridge lemmas

These connect the cycle polynomials to real cyclotomic minimal polynomials
via the substitution u = i/x where i² = −1.

The key identities (purely algebraic, no cyclotomic theory):
- 3-cycle: f(x) = 3x⁶+9x⁴+6x²+1 vanishes iff m₃₆(i/x) = 0
  where m₃₆(u) = u⁶ − 6u⁴ + 9u² − 3
- 4-cycle quartic: B(x) = 2x⁴+4x²+1 vanishes iff m₁₆(i/x) = 0
  where m₁₆(u) = u⁴ − 4u² + 2
- 4-cycle octic: C(x) = x⁸+7x⁶+14x⁴+8x²+1 vanishes iff m₆₀*(i/x) = 0
  where m₆₀*(u) = u⁸ − 8u⁶ + 14u⁴ − 7u² + 1

Once these are established, the sorry targets reduce to:
  "mₙ has a root in 𝔽_q iff q ≡ ±1 (mod N)"
which is the irreducible cyclotomic/Frobenius core. -/

/-- **3-cycle substitution bridge**.
The 3-cycle polynomial 3x⁶ + 9x⁴ + 6x² + 1 vanishes at x ≠ 0
if and only if the real cyclotomic polynomial m₃₆(u) = u⁶ − 6u⁴ + 9u² − 3
vanishes at u = i/x, where i² = −1.

This is a pure algebraic identity: after substituting i² = −1 and clearing
denominators, both sides reduce to the same polynomial equation. -/
theorem three_cycle_poly_iff_m36 {x i : K} (hx : x ≠ 0) (hi : i ^ 2 = -1) :
    3 * x ^ 6 + 9 * x ^ 4 + 6 * x ^ 2 + 1 = 0 ↔
    (i / x) ^ 6 - 6 * (i / x) ^ 4 + 9 * (i / x) ^ 2 - 3 = 0 := by
  have hi4 := sq_neg_one_pow_four hi
  have hi6 := sq_neg_one_pow_six hi
  have hx6 : (x : K) ^ 6 ≠ 0 := pow_ne_zero 6 hx
  rw [div_pow, div_pow, div_pow, hi6, hi4, hi]
  -- After reduction: LHS is 3x⁶+9x⁴+6x²+1 = 0
  -- RHS becomes (-1)/x⁶ - 6·(1/x⁴) + 9·(-1/x²) - 3 = 0
  -- i.e. -1/x⁶ - 6/x⁴ - 9/x² - 3 = 0
  -- Multiply by -x⁶: 1 + 6x² + 9x⁴ + 3x⁶ = 0, which is the LHS.
  constructor <;> intro h
  · have : -(1 : K) / x ^ 6 - 6 * ((1 : K) / x ^ 4) + 9 * (-(1 : K) / x ^ 2) - 3 =
        -(3 * x ^ 6 + 9 * x ^ 4 + 6 * x ^ 2 + 1) / x ^ 6 := by field_simp; ring
    rw [this, h]; simp
  · have key : 3 * x ^ 6 + 9 * x ^ 4 + 6 * x ^ 2 + 1 =
        -(x ^ 6 * (-1 / x ^ 6 - 6 * (1 / x ^ 4) + 9 * (-1 / x ^ 2) - 3)) := by
      field_simp; ring
    rw [key, h, mul_zero, neg_zero]

/-- **4-cycle quartic substitution bridge**.
The quartic 4-cycle factor 2x⁴ + 4x² + 1 vanishes at x ≠ 0
if and only if the real cyclotomic polynomial m₁₆(u) = u⁴ − 4u² + 2
vanishes at u = i/x, where i² = −1.

m₁₆ is the minimal polynomial of 2cos(π/8) = ζ₁₆ + ζ₁₆⁻¹ over ℚ. -/
theorem four_cycle_quartic_iff_m16 {x i : K} (hx : x ≠ 0) (hi : i ^ 2 = -1) :
    2 * x ^ 4 + 4 * x ^ 2 + 1 = 0 ↔
    (i / x) ^ 4 - 4 * (i / x) ^ 2 + 2 = 0 := by
  have hi4 := sq_neg_one_pow_four hi
  rw [div_pow, div_pow, hi4, hi]
  -- After reduction: RHS is 1/x⁴ + 4/x² + 2 = 0
  -- Multiply by x⁴: 1 + 4x² + 2x⁴ = 0 = LHS
  constructor <;> intro h
  · have : (1 : K) / x ^ 4 - 4 * (-(1 : K) / x ^ 2) + 2 =
        (2 * x ^ 4 + 4 * x ^ 2 + 1) / x ^ 4 := by field_simp; ring
    rw [this, h]; simp
  · have key : 2 * x ^ 4 + 4 * x ^ 2 + 1 =
        x ^ 4 * (1 / x ^ 4 - 4 * (-1 / x ^ 2) + 2) := by
      field_simp; ring
    rw [key, h, mul_zero]

/-- **4-cycle octic substitution bridge**.
The octic 4-cycle factor x⁸ + 7x⁶ + 14x⁴ + 8x² + 1 vanishes at x ≠ 0
if and only if the reciprocal of the real cyclotomic polynomial
m₆₀*(u) = u⁸ − 8u⁶ + 14u⁴ − 7u² + 1 vanishes at u = i/x.

m₆₀ is the minimal polynomial of 2cos(π/30) = ζ₆₀ + ζ₆₀⁻¹ over ℚ, and
m₆₀*(u) = u⁸ · m₆₀(1/u) is its reciprocal polynomial. -/
theorem four_cycle_octic_iff_m60 {x i : K} (hx : x ≠ 0) (hi : i ^ 2 = -1) :
    x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1 = 0 ↔
    (i / x) ^ 8 - 8 * (i / x) ^ 6 + 14 * (i / x) ^ 4 -
      7 * (i / x) ^ 2 + 1 = 0 := by
  have hi4 := sq_neg_one_pow_four hi
  have hi6 := sq_neg_one_pow_six hi
  have hi8 := sq_neg_one_pow_eight hi
  rw [div_pow, div_pow, div_pow, div_pow, hi8, hi6, hi4, hi]
  -- After reduction: RHS is 1/x⁸ + 8/x⁶ + 14/x⁴ + 7/x² + 1 = 0
  -- Multiply by x⁸: 1 + 8x² + 14x⁴ + 7x⁶ + x⁸ = C(x) = 0
  constructor <;> intro h
  · have : (1 : K) / x ^ 8 - 8 * (-(1 : K) / x ^ 6) + 14 * ((1 : K) / x ^ 4) -
        7 * (-(1 : K) / x ^ 2) + 1 =
        (x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1) / x ^ 8 := by
      field_simp; ring
    rw [this, h]; simp
  · have key : x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1 =
        x ^ 8 * (1 / x ^ 8 - 8 * (-1 / x ^ 6) + 14 * (1 / x ^ 4) -
          7 * (-1 / x ^ 2) + 1) := by
      field_simp; ring
    rw [key, h, mul_zero]

/-! ## Layer G: Three-cycle ↔ m₃₆ root in K

This bridges the combinatorial 3-cycle condition (∃ x ≠ 0, θ³(x) = x ∧ θ²(x) ≠ x ∧ θ(x) ≠ x)
to the algebraic condition (∃ u, m₃₆(u) = 0) where m₃₆(u) = u⁶ − 6u⁴ + 9u² − 3.

The proof combines `three_cycle_poly_iff` and `three_cycle_poly_iff_m36` with the
invertible substitution x ↔ i/x (where i² = −1). -/

/-- Side condition: if 3x⁶+9x⁴+6x²+1 = 0 then x²+1 ≠ 0.
    Proof: substituting x²=-1 gives 3(-1)+9(1)+6(-1)+1 = 1 ≠ 0. -/
lemma m36_poly_side_h1 {x : K}
    (hpoly : 3 * x ^ 6 + 9 * x ^ 4 + 6 * x ^ 2 + 1 = 0) :
    x ^ 2 + 1 ≠ 0 := by
  intro h1
  exact one_ne_zero (show (1 : K) = 0 by linear_combination hpoly - (3 * x ^ 4 + 6 * x ^ 2) * h1)

/-- Side condition: if 3x⁶+9x⁴+6x²+1 = 0 and x ≠ 0 then x⁴+3x²+1 ≠ 0.
    Proof: the two equations together give 3x²+1 = 0, then x⁴ = 0, contradicting x ≠ 0. -/
lemma m36_poly_side_h2 {x : K} (hx : x ≠ 0)
    (hpoly : 3 * x ^ 6 + 9 * x ^ 4 + 6 * x ^ 2 + 1 = 0) :
    x ^ 4 + 3 * x ^ 2 + 1 ≠ 0 := by
  intro h2
  have h3x2 : 3 * x ^ 2 + 1 = 0 := by linear_combination hpoly - 3 * x ^ 2 * h2
  exact pow_ne_zero 4 hx (show x ^ 4 = 0 by linear_combination h2 - h3x2)

set_option maxHeartbeats 400000 in
/-- Three-cycle iff m36 root. -/
theorem three_cycle_iff_m36_root_in_K (hchar2 : ringChar K ≠ 2) (hchar3 : ringChar K ≠ 3)
    (hsplit : ∃ i : K, i ^ 2 = -1) :
    (∃ x : K, x ≠ 0 ∧ theta3 x = x ∧ theta2 x ≠ x ∧ theta x ≠ x) ↔
    (∃ u : K, u ^ 6 - 6 * u ^ 4 + 9 * u ^ 2 - 3 = 0) := by
  obtain ⟨i, hi⟩ := hsplit
  have hi_ne : i ≠ 0 := by intro h; simp [h] at hi
  constructor
  · -- Forward: 3-cycle → m₃₆ root via substitution u = i/x
    rintro ⟨x, hx, h3x, h2x, h1x⟩
    have h1 : x ^ 2 + 1 ≠ 0 := by
      intro h1
      have hθ0 : theta x = 0 := by rw [theta_eq_div hx, h1]; simp
      have hθ30 : theta3 x = 0 := theta2_zero_imp_theta3_zero (theta_zero_imp_theta2_zero hθ0)
      exact hx (h3x ▸ hθ30)
    have h2 : x ^ 4 + 3 * x ^ 2 + 1 ≠ 0 := by
      intro h2
      have hθ20 : theta2 x = 0 := by rw [theta2_eq_div hx h1, h2]; simp
      have hθ30 : theta3 x = 0 := theta2_zero_imp_theta3_zero hθ20
      exact hx (h3x ▸ hθ30)
    have hpoly := (three_cycle_poly_iff hx hchar2 hchar3 h1 h2).mp ⟨h3x, h2x, h1x⟩
    exact ⟨i / x, (three_cycle_poly_iff_m36 hx hi).mp hpoly⟩
  · -- Backward: m₃₆ root → 3-cycle via substitution x = i/u
    rintro ⟨u, hu⟩
    have h3ne : (3 : K) ≠ 0 := by
      intro h3; apply hchar3
      have h3d : ringChar K ∣ 3 := (ringChar.spec K 3).mp (by exact_mod_cast h3)
      rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | hp
      · exact ((Nat.dvd_prime Nat.prime_three).mp h3d).resolve_left hp.one_lt.ne'
      · simp [hp] at h3d
    have hu_ne : u ≠ 0 := by intro h; simp [h] at hu; exact h3ne hu
    have hx : (i / u : K) ≠ 0 := div_ne_zero hi_ne hu_ne
    have hix : i / (i / u) = u := by field_simp
    have hpoly : 3 * (i / u) ^ 6 + 9 * (i / u) ^ 4 + 6 * (i / u) ^ 2 + 1 = 0 := by
      exact (three_cycle_poly_iff_m36 hx hi).mpr (by rw [hix]; exact hu)
    have hcycle := (three_cycle_poly_iff hx hchar2 hchar3
      (m36_poly_side_h1 hpoly) (m36_poly_side_h2 hx hpoly)).mpr hpoly
    exact ⟨i / u, hx, hcycle.1, hcycle.2.1, hcycle.2.2⟩

/-! ## Layer C: Frobenius compatibility with theta

The Frobenius endomorphism x ↦ x^q commutes with theta: θ(a)^q = θ(a^q).
This follows from (a + a⁻¹)^q = a^q + (a⁻¹)^q in characteristic p,
using add_pow_char_pow and inv_pow. -/

/-- Frobenius commutes with theta: θ(a)^q = θ(a^q) for all a in a finite field.
This holds unconditionally (including a = 0). -/
lemma frobenius_theta_comm (a : K) :
    (theta a) ^ Fintype.card K = theta (a ^ Fintype.card K) := by
  simp only [theta_def]
  obtain ⟨p, _, n, hprime, hcard⟩ := FiniteField.card' K
  haveI : Fact (Nat.Prime p) := ⟨hprime⟩
  rw [hcard, add_pow_char_pow, inv_pow]

/-! ## Layer B: Chebyshev root identity

If ζ is a primitive 36th root of unity, then u = ζ + ζ⁻¹ is a root of
m₃₆(u) = u⁶ - 6u⁴ + 9u² - 3.

The proof factors through cyclotomic 6: since ζ⁶ is a primitive 6th root,
it satisfies X² - X + 1 = 0, giving ζ¹² - ζ⁶ + 1 = 0. Then a
field_simp + ring computation shows m₃₆(ζ + ζ⁻¹) = (ζ¹² - ζ⁶ + 1)/ζ⁶ = 0. -/

/-- A primitive 36th root gives a root of m₃₆ via the Chebyshev substitution. -/
lemma isPrimitiveRoot_36_implies_m36_root {ζ : K} (hζ : IsPrimitiveRoot ζ 36) :
    (ζ + ζ⁻¹) ^ 6 - 6 * (ζ + ζ⁻¹) ^ 4 + 9 * (ζ + ζ⁻¹) ^ 2 - 3 = 0 := by
  have hζ_ne : ζ ≠ 0 := by
    intro h; subst h; exact absurd hζ (by intro h; have := h.pow_eq_one; simp at this)
  -- ζ⁶ is a primitive 6th root, so it satisfies cyclotomic 6 = X² - X + 1
  have h6 : ζ ^ 12 - ζ ^ 6 + 1 = 0 := by
    have hprim6 := hζ.pow (by norm_num) (show 36 = 6 * 6 by norm_num)
    have hroot := hprim6.isRoot_cyclotomic (show 0 < 6 by norm_num)
    rw [Polynomial.cyclotomic_six] at hroot
    simp [Polynomial.IsRoot] at hroot
    have : (ζ ^ 6) ^ 2 = ζ ^ 12 := by ring
    rw [this] at hroot; exact hroot
  -- m₃₆(ζ + ζ⁻¹) = (ζ¹² - ζ⁶ + 1) / ζ⁶ = 0
  have hζ6 : ζ ^ 6 ≠ 0 := pow_ne_zero 6 hζ_ne
  have key : ζ ^ 6 * ((ζ + ζ⁻¹) ^ 6 - 6 * (ζ + ζ⁻¹) ^ 4 + 9 * (ζ + ζ⁻¹) ^ 2 - 3) = 0 := by
    have : ζ ^ 6 * ((ζ + ζ⁻¹) ^ 6 - 6 * (ζ + ζ⁻¹) ^ 4 + 9 * (ζ + ζ⁻¹) ^ 2 - 3) =
        (1 - ζ ^ 6 + ζ ^ 12) / 1 := by field_simp; ring
    rw [this, div_one]; linear_combination h6
  exact (mul_eq_zero.mp key).resolve_left hζ6

/-! ## Layer E1: Backward direction of the Frobenius root criterion

If q ≡ 1 (mod 36) then m₃₆ has a root in K. The proof:
1. 36 ∣ (q - 1) = |Kˣ|.
2. Kˣ is cyclic (Mathlib instance), so there exists g ∈ Kˣ with orderOf g = 36
   (since φ(36) > 0 elements of order 36 exist when 36 ∣ |Kˣ|).
3. g is a primitive 36th root of unity in K.
4. By Layer B, u = g + g⁻¹ is a root of m₃₆. -/

/-- If q ≡ 1 (mod 36), then m₃₆(u) = u⁶ - 6u⁴ + 9u² - 3 has a root in K. -/
lemma m36_root_of_mod36 (hmod : Fintype.card K % 36 = 1) :
    ∃ u : K, u ^ 6 - 6 * u ^ 4 + 9 * u ^ 2 - 3 = 0 := by
  -- 36 ∣ (q - 1) = |Kˣ|
  have hdvd : 36 ∣ Fintype.card Kˣ := by rw [Fintype.card_units]; omega
  -- {g : Kˣ | orderOf g = 36} has cardinality φ(36) > 0, so pick one
  have hcard := IsCyclic.card_orderOf_eq_totient hdvd
  obtain ⟨g, hg⟩ := Finset.card_pos.mp (hcard ▸ Nat.totient_pos.mpr (by norm_num))
  simp at hg
  -- g is a primitive 36th root of unity in K
  have hprim : IsPrimitiveRoot (g : K) 36 :=
    IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hg)
  exact ⟨(g : K) + (g : K)⁻¹, isPrimitiveRoot_36_implies_m36_root hprim⟩

/-! ## Layer F: Modular arithmetic elimination

If q = 1 mod 4 then q cannot be 35 mod 36 (i.e. -1 mod 36),
since 35 mod 4 = 3, not 1. This is used in the forward direction of
the 3-cycle criterion to rule out the q = -1 mod 36 case. -/

/-- q = 1 mod 4 and q = 35 mod 36 is impossible. -/
lemma not_neg_one_mod_36_of_one_mod_4 {q : ℕ}
    (h4 : q % 4 = 1) (h36 : q % 36 = 35) : False := by
  omega

/-! ## Layer E2: Forward Frobenius direction (partial)

The forward direction of the cyclotomic criterion: if m36 has a root u in K,
then q = 1 mod 36.  The proof case-splits on whether the quadratic X^2-uX+1
has a root in K.

**Case 1** (quadratic splits): a root zeta in K is a primitive 36th root of
unity, so 36 | (q-1) and q = 1 mod 36.  This case is fully verified.

**Case 2** (quadratic irreducible): zeta lives in a degree-2 extension L.
The Frobenius x -> x^q maps zeta to zeta^(-1) (the other root), giving
zeta^(q+1) = 1, so 36 | (q+1), i.e. q = 35 mod 36.  This contradicts
q = 1 mod 4 by Layer F.  This case uses AdjoinRoot and Frobenius
on the quadratic extension (fully verified). -/

/-- Ring identity: if zeta^2 - u*zeta + 1 = 0 and m36(u) = 0, then
zeta^12 - zeta^6 + 1 = 0.  This is the converse of the Chebyshev identity
from Layer B: zeta^6 * m36(zeta + zeta^(-1)) = zeta^12 - zeta^6 + 1. -/
lemma root_quad_satisfies_cyc6 {R : Type*} [Field R] {u ζ : R}
    (hquad : ζ ^ 2 - u * ζ + 1 = 0)
    (hm36 : u ^ 6 - 6 * u ^ 4 + 9 * u ^ 2 - 3 = 0) :
    ζ ^ 12 - ζ ^ 6 + 1 = 0 := by
  have hζne : ζ ≠ 0 := by intro h; simp [h] at hquad
  have hsum : ζ + ζ⁻¹ = u := by
    have h1 : u * ζ = ζ ^ 2 + 1 := by linear_combination -hquad
    field_simp; linear_combination -h1
  have hcheb : ζ ^ 6 * (u ^ 6 - 6 * u ^ 4 + 9 * u ^ 2 - 3) = ζ ^ 12 - ζ ^ 6 + 1 := by
    rw [← hsum]
    have h : ζ ^ 6 * ((ζ + ζ⁻¹) ^ 6 - 6 * (ζ + ζ⁻¹) ^ 4 + 9 * (ζ + ζ⁻¹) ^ 2 - 3) =
        (1 - ζ ^ 6 + ζ ^ 12) / 1 := by field_simp; ring
    rw [h, div_one]; ring
  rw [hm36, mul_zero] at hcheb; exact hcheb.symm

set_option maxHeartbeats 400000 in
/-- If zeta^2 - u*zeta + 1 = 0 and m36(u) = 0 in a field with char != 2, 3,
then zeta is a primitive 36th root of unity.  The proof shows orderOf = 36
by establishing zeta^36 = 1, zeta^18 != 1 (char != 2), zeta^12 != 1
(char != 3), and checking that 36 is the only divisor of 36 not dividing
18 or 12. -/
lemma isPrimitiveRoot_of_quad_m36_root {R : Type*} [Field R]
    (hchar2 : ringChar R ≠ 2) (hchar3 : ringChar R ≠ 3)
    {u ζ : R} (hquad : ζ ^ 2 - u * ζ + 1 = 0)
    (hm36 : u ^ 6 - 6 * u ^ 4 + 9 * u ^ 2 - 3 = 0) :
    IsPrimitiveRoot ζ 36 := by
  have hcyc := root_quad_satisfies_cyc6 hquad hm36
  have hζne : ζ ≠ 0 := by intro h; simp [h] at hquad
  have h18 : ζ ^ 18 = -1 := by linear_combination (ζ ^ 6 + 1) * hcyc
  have h36 : ζ ^ 36 = 1 := by
    calc ζ ^ 36 = (ζ ^ 18) ^ 2 := by ring
    _ = (-1) ^ 2 := by rw [h18]
    _ = 1 := by ring
  have h18ne : ζ ^ 18 ≠ 1 := by
    rw [h18]; intro h
    have h2 : (2 : R) = 0 := by linear_combination -h
    apply hchar2
    have h2d : ringChar R ∣ 2 := (ringChar.spec R 2).mp (by exact_mod_cast h2)
    have hp := CharP.char_is_prime_or_zero R (ringChar R)
    rcases hp with hp | hp
    · exact Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h2d) hp.two_le
    · simp [hp] at h2d
  have h12ne : ζ ^ 12 ≠ 1 := by
    intro h12
    have h6 : ζ ^ 6 = 2 := by linear_combination -hcyc + h12
    have h3 : (3 : R) = 0 := by
      have key := hcyc
      rw [show ζ ^ 12 = (ζ ^ 6) ^ 2 from by ring, h6] at key
      norm_num at key; exact key
    apply hchar3
    have h3d : ringChar R ∣ 3 := (ringChar.spec R 3).mp (by exact_mod_cast h3)
    have hp := CharP.char_is_prime_or_zero R (ringChar R)
    rcases hp with hp | hp
    · exact (Nat.dvd_prime Nat.prime_three).mp h3d |>.resolve_left hp.one_lt.ne'
    · simp [hp] at h3d
  have hord_dvd : orderOf ζ ∣ 36 := orderOf_dvd_of_pow_eq_one h36
  have hord_not18 : ¬(orderOf ζ ∣ 18) := by rwa [orderOf_dvd_iff_pow_eq_one]
  have hord_not12 : ¬(orderOf ζ ∣ 12) := by rwa [orderOf_dvd_iff_pow_eq_one]
  have hord : orderOf ζ = 36 := by
    have hle : orderOf ζ ≤ 36 := Nat.le_of_dvd (by norm_num) hord_dvd
    have hpos : 0 < orderOf ζ := Nat.pos_of_dvd_of_pos hord_dvd (by norm_num)
    interval_cases (orderOf ζ) <;> omega
  exact IsPrimitiveRoot.iff_orderOf.mpr hord

/-- If X^2-uX+1 has a root in K and m36(u) = 0, then q = 1 mod 36.
The root is a primitive 36th root, so 36 | |K*| = q-1. -/
lemma mod36_of_quad_root_in_K (hchar2 : ringChar K ≠ 2) (hchar3 : ringChar K ≠ 3)
    {u ζ : K} (hm36 : u ^ 6 - 6 * u ^ 4 + 9 * u ^ 2 - 3 = 0)
    (hquad : ζ ^ 2 - u * ζ + 1 = 0) :
    Fintype.card K % 36 = 1 := by
  have hζne : ζ ≠ 0 := by intro h; simp [h] at hquad
  have hprim : IsPrimitiveRoot ζ 36 :=
    isPrimitiveRoot_of_quad_m36_root hchar2 hchar3 hquad hm36
  have hprim_unit : IsPrimitiveRoot (Units.mk0 ζ hζne) 36 :=
    IsPrimitiveRoot.coe_units_iff.mp hprim
  have hdvd : 36 ∣ Fintype.card Kˣ :=
    (IsPrimitiveRoot.iff_orderOf.mp hprim_unit) ▸ orderOf_dvd_card
  rw [Fintype.card_units] at hdvd
  have hcard_pos : Fintype.card K ≥ 1 := Fintype.card_pos
  omega

/-- If both ζ and η satisfy X²-uX+1 = 0, then η = ζ or η = ζ⁻¹.
The quadratic factors as (X-ζ)(X-ζ⁻¹), so any root is one of these. -/
lemma quad_root_eq_or_inv {R : Type*} [Field R] {ζ η u : R}
    (hζ : ζ ^ 2 - u * ζ + 1 = 0) (hη : η ^ 2 - u * η + 1 = 0) :
    η = ζ ∨ η = ζ⁻¹ := by
  have key : (η - ζ) * (η - (u - ζ)) = 0 := by ring_nf; linear_combination hη - hζ
  have hinv : u - ζ = ζ⁻¹ := by
    symm; rw [inv_eq_iff_eq_inv]
    exact eq_inv_of_mul_eq_one_right (by linear_combination -hζ)
  rcases mul_eq_zero.mp key with h | h
  · left; exact sub_eq_zero.mp h
  · right; rw [← hinv]; exact sub_eq_zero.mp h

omit [DecidableEq K] in
/-- Root of an irreducible quadratic over F_q is not fixed by Frobenius.
If f is irreducible with deg f = 2, then (AdjoinRoot.root f)^q ≠ root,
because f ∤ X^q-X (all irreducible factors of X^q-X have degree 1). -/
lemma adjoinRoot_root_pow_card_ne {f : Polynomial K}
    (hirr : Irreducible f) (hdeg : f.natDegree = 2) :
    AdjoinRoot.root f ^ Fintype.card K ≠ AdjoinRoot.root f := by
  intro heq
  have hmk : AdjoinRoot.mk f (Polynomial.X ^ Fintype.card K - Polynomial.X) = 0 := by
    simp only [map_sub, map_pow, AdjoinRoot.mk_X]; exact sub_eq_zero.mpr heq
  rw [AdjoinRoot.mk_eq_zero] at hmk
  have hsplits : (Polynomial.map (algebraMap K K)
      (Polynomial.X ^ Fintype.card K - Polynomial.X)).Splits :=
    Polynomial.IsSplittingField.splits K (Polynomial.X ^ Fintype.card K - Polynomial.X)
  rw [show algebraMap K K = RingHom.id K from rfl, Polynomial.map_id] at hsplits
  have hne : (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K) ≠ 0 := by
    intro h0
    have hsub : ((Polynomial.X : Polynomial K) ^ Fintype.card K -
        Polynomial.X).natDegree = Fintype.card K := by
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
      · exact Polynomial.natDegree_X_pow _
      · rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
        have := Fintype.one_lt_card (α := K); omega
    rw [h0] at hsub; simp at hsub
    exact absurd hsub.symm (by have := Fintype.one_lt_card (α := K); omega)
  exact absurd (hsplits.of_dvd hne hmk |>.degree_eq_one_of_irreducible hirr) (by
    rw [Polynomial.degree_eq_natDegree (Irreducible.ne_zero hirr), hdeg]; norm_num)

set_option maxHeartbeats 400000 in
/-- q ≡ 1 (mod 4) when -1 is a square in F_q (and char ≠ 2).
If i² = -1, then orderOf i = 4, so 4 | (q-1). -/
lemma mod4_of_neg_one_is_square (hchar2 : ringChar K ≠ 2)
    (hsplit : ∃ i : K, i ^ 2 = -1) :
    Fintype.card K % 4 = 1 := by
  obtain ⟨i, hi⟩ := hsplit
  have hine : i ≠ 0 := by
    intro h; rw [h, zero_pow (by norm_num : 2 ≠ 0)] at hi
    exact absurd (neg_eq_zero.mp hi.symm) one_ne_zero
  have hi4 : i ^ 4 = 1 := by
    have : i ^ 4 = (i ^ 2) ^ 2 := by ring
    rw [this, hi]; ring
  have neg_one_ne_one : (-1 : K) ≠ 1 := by
    intro h
    have h20 : (2 : K) = 0 := by linear_combination -h
    apply hchar2
    have h2d : ringChar K ∣ 2 := (ringChar.spec K 2).mp (by exact_mod_cast h20)
    have hp := CharP.char_is_prime_or_zero K (ringChar K)
    rcases hp with hp | hp
    · exact Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h2d) hp.two_le
    · simp [hp] at h2d
  have hi2ne : i ^ 2 ≠ 1 := by rw [hi]; exact neg_one_ne_one
  set iu := Units.mk0 i hine
  have hi4u : iu ^ 4 = 1 := by ext; push_cast; exact hi4
  have hi2u : iu ^ 2 ≠ 1 := by
    intro h; apply hi2ne
    have := congr_arg Units.val h
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at this; exact this
  have hord : orderOf iu = 4 := by
    have hd : orderOf iu ∣ 4 := orderOf_dvd_of_pow_eq_one hi4u
    have hn2 : ¬(orderOf iu ∣ 2) := by rwa [orderOf_dvd_iff_pow_eq_one]
    have hle : orderOf iu ≤ 4 := Nat.le_of_dvd (by norm_num) hd
    interval_cases (orderOf iu) <;> simp_all
  have hdvd : 4 ∣ Fintype.card Kˣ := hord ▸ orderOf_dvd_card
  rw [Fintype.card_units] at hdvd
  have hcard_pos : Fintype.card K ≥ 1 := Fintype.card_pos
  omega

set_option maxHeartbeats 1600000 in
/-- Forward direction of the cyclotomic root criterion: if m36 has a root
in K (with q = 1 mod 4), then q = 1 mod 36.  Case-splits on whether the
quadratic X^2-uX+1 has a root in K. -/
lemma mod36_of_m36_root (hchar2 : ringChar K ≠ 2) (hchar3 : ringChar K ≠ 3)
    (hsplit : ∃ i : K, i ^ 2 = -1)
    (hroot : ∃ u : K, u ^ 6 - 6 * u ^ 4 + 9 * u ^ 2 - 3 = 0) :
    Fintype.card K % 36 = 1 := by
  obtain ⟨u, hm36⟩ := hroot
  by_cases h : ∃ ζ : K, ζ ^ 2 - u * ζ + 1 = 0
  · -- Case 1: X²-uX+1 splits over K
    obtain ⟨ζ, hquad⟩ := h
    exact mod36_of_quad_root_in_K hchar2 hchar3 hm36 hquad
  · -- Case 2: X²-uX+1 irreducible over K
    -- Build AdjoinRoot of f = X²-uX+1; its root ζ is a primitive 36th root.
    -- Frobenius maps ζ → ζ⁻¹ (since ζ ∉ K), giving ζ^(q+1) = 1.
    -- Then 36 | (q+1), so q ≡ 35 mod 36, contradicting q ≡ 1 mod 4.
    push_neg at h
    exfalso
    set f := (Polynomial.X ^ 2 - Polynomial.C u * Polynomial.X + 1 : Polynomial K) with hf_def
    -- f is irreducible (degree 2 with no roots)
    have hf_irr : Irreducible f := by
      apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
      · show f.natDegree ∈ Finset.Icc 1 3
        have : f.natDegree = 2 := by
          show (Polynomial.X ^ 2 - Polynomial.C u * Polynomial.X + 1 :
            Polynomial K).natDegree = 2
          compute_degree!
        rw [this]; decide
      · intro a; simp [Polynomial.IsRoot, hf_def]; exact h a
    haveI : Fact (Irreducible f) := ⟨hf_irr⟩
    set L := AdjoinRoot f
    set ζ := AdjoinRoot.root f
    set u_L := algebraMap K L u
    -- Get characteristic p and cardinality q = p^n
    obtain ⟨p, hp, npos, hprime, hcard⟩ := FiniteField.card' K
    set n := (npos : ℕ)
    haveI : Fact (Nat.Prime p) := ⟨hprime⟩
    haveI : CharP L p :=
      charP_of_injective_algebraMap (algebraMap K L).injective p
    -- Transfer ringChar to L
    have hcharL2 : ringChar L ≠ 2 := by
      rw [ringChar.eq L p, ← ringChar.eq K p]; exact hchar2
    have hcharL3 : ringChar L ≠ 3 := by
      rw [ringChar.eq L p, ← ringChar.eq K p]; exact hchar3
    -- ζ satisfies the quadratic ζ²-u_L·ζ+1 = 0
    have hquad : ζ ^ 2 - u_L * ζ + 1 = 0 := by
      have hev := @AdjoinRoot.eval₂_root K _ f
      change Polynomial.eval₂ (AdjoinRoot.of f) ζ
        (Polynomial.X ^ 2 - Polynomial.C u * Polynomial.X + 1) = 0 at hev
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_mul,
                 Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
                 Polynomial.eval₂_one] at hev
      exact hev
    have hζne : ζ ≠ 0 := by intro hz; simp [hz] at hquad
    have hdeg : f.natDegree = 2 := by
      show (Polynomial.X ^ 2 - Polynomial.C u * Polynomial.X + 1 :
        Polynomial K).natDegree = 2
      compute_degree!
    -- ζ^q ≠ ζ (root of irreducible quadratic is not Frobenius-fixed)
    have hne : ζ ^ Fintype.card K ≠ ζ := adjoinRoot_root_pow_card_ne hf_irr hdeg
    -- Frobenius fixes u_L (since u ∈ K)
    have hu_fixed : u_L ^ Fintype.card K = u_L := by
      show (algebraMap K L u) ^ Fintype.card K = algebraMap K L u
      rw [← map_pow, FiniteField.pow_card]
    -- Frobenius: (ζ^q)²-u_L·(ζ^q)+1 = 0
    -- Uses: ζ²=u_L·ζ-1, then (ζ²)^q = (u_L·ζ+(-1))^q = u_L^q·ζ^q+(-1)^q
    have hquad_q : (ζ ^ Fintype.card K) ^ 2 - u_L * (ζ ^ Fintype.card K) + 1 = 0 := by
      have hζ2 : ζ ^ 2 = u_L * ζ - 1 := by linear_combination hquad
      have key : (ζ ^ 2) ^ Fintype.card K = u_L * ζ ^ Fintype.card K - 1 := by
        conv_lhs => rw [hζ2, show u_L * ζ - 1 = u_L * ζ + (-1) from by ring]
        rw [hcard, add_pow_char_pow _ _ p n, mul_pow, ← hcard, hu_fixed,
            hcard, neg_one_pow_char_pow _ p n, ← hcard]; ring
      have h1 : (ζ ^ Fintype.card K) ^ 2 = (ζ ^ 2) ^ Fintype.card K := by ring
      rw [h1, key]; ring
    -- Both ζ and ζ^q are roots of X²-u_L·X+1, so ζ^q ∈ {ζ, ζ⁻¹}
    -- Since ζ^q ≠ ζ, we get ζ^q = ζ⁻¹
    have hζq_inv : ζ ^ Fintype.card K = ζ⁻¹ :=
      (quad_root_eq_or_inv hquad hquad_q).resolve_left hne
    -- ζ^(q+1) = ζ·ζ⁻¹ = 1
    have hpow : ζ ^ (Fintype.card K + 1) = 1 := by
      rw [pow_succ, hζq_inv, inv_mul_cancel₀ hζne]
    -- m₃₆(u_L) = 0 (lifted from K via algebraMap)
    have hm36_L : u_L ^ 6 - 6 * u_L ^ 4 + 9 * u_L ^ 2 - 3 = 0 := by
      have : (algebraMap K L) (u ^ 6 - 6 * u ^ 4 + 9 * u ^ 2 - 3) = 0 := by
        rw [hm36]; simp
      simp only [map_sub, map_add, map_mul, map_pow, map_ofNat] at this; exact this
    -- ζ is a primitive 36th root of unity in L
    have hprim := isPrimitiveRoot_of_quad_m36_root hcharL2 hcharL3 hquad hm36_L
    -- From ζ^(q+1) = 1 and orderOf ζ = 36: 36 | (q+1)
    have hord36 : orderOf ζ = 36 := IsPrimitiveRoot.iff_orderOf.mp hprim
    have hdvd : 36 ∣ (Fintype.card K + 1) := hord36 ▸ orderOf_dvd_of_pow_eq_one hpow
    -- So q ≡ 35 (mod 36)
    have hmod36 : Fintype.card K % 36 = 35 := by omega
    -- But q ≡ 1 (mod 4) from hsplit
    have hmod4 := mod4_of_neg_one_is_square hchar2 hsplit
    -- Contradiction: 35 mod 4 = 3 ≠ 1
    exact not_neg_one_mod_36_of_one_mod_4 hmod4 hmod36

/-! ## Cyclotomic existence criteria

Layers E1 (backward) and E2 (forward) are both fully verified, completing
the 3-cycle criterion.
The 4-cycle count formula requires analogous arguments for m16 and m60. -/

/-- **Three-cycle existence criterion** (split case q = 1 mod 4, char != 3).
theta has a genuine affine 3-cycle over F_q if and only if q = 1 (mod 36).
When this holds, there are exactly two such 3-cycles. -/
theorem three_cycle_existence_iff_mod36 (hchar2 : ringChar K ≠ 2) (hchar3 : ringChar K ≠ 3)
    (hsplit : ∃ i : K, i ^ 2 = -1) -- i.e. q ≡ 1 (mod 4)
    :
    (∃ x : K, x ≠ 0 ∧ theta3 x = x ∧ theta2 x ≠ x ∧ theta x ≠ x) ↔
    (Fintype.card K) % 36 = 1 := by
  rw [three_cycle_iff_m36_root_in_K hchar2 hchar3 hsplit]
  exact ⟨fun h => mod36_of_m36_root hchar2 hchar3 hsplit h,
         fun h => m36_root_of_mod36 h⟩

-- The four-cycle count formula has been moved to `ThetaFourCycleHelpers.lean`
-- as `four_cycle_count_formula'`, where all the cyclotomic infrastructure
-- (m₁₆, m₆₀ criteria, root counting, etc.) is available.
-- It cannot be proved here due to circular import constraints:
-- ThetaFourCycleHelpers imports ThetaCycles, so ThetaCycles cannot
-- import ThetaFourCycleHelpers.
--
-- Statement (fully proved in ThetaFourCycleHelpers.lean):
--   theorem four_cycle_count_formula' (hchar2 : ringChar K ≠ 2)
--       (hsplit : ∃ i : K, i ^ 2 = -1) :
--       (Finset.univ.filter (fun x : K =>
--         x ≠ 0 ∧ theta4 x = x ∧ theta2 x ≠ x)).card / 4 =
--       (if (Fintype.card K) % 16 = 1 then 1 else 0) +
--       2 * (if (Fintype.card K) % 60 = 1 then 1 else 0)

end