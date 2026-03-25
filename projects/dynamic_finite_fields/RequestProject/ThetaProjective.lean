import Mathlib
import RequestProject.ThetaMap

/-!
# Projective Extension of θ(x) = x + x⁻¹

We extend the theta map to the projective line P¹(F_q), modeled as `Option K`
(where `none` represents the point at infinity), and prove:

- The projective fiber law
- The projective indegree classification
- The projective image-size formula |Im(θ : P¹ → P¹)| = (q + 3) / 2
- A clean two-cycle existence criterion

## Projective extension

We define θ on P¹ by:
  θ(∞) = ∞
  θ(0) = ∞
  θ(x) = x + x⁻¹  for x ≠ 0

## Main results

- `thetaP1_eq_none_iff`: The fiber above ∞ is exactly {0, ∞}
- `thetaP1_eq_some_iff`: The affine fiber law on P¹
- `thetaP1_indeg_inf`: ∞ has indegree 2 on P¹
- `thetaP1_indeg_le_two`: Every vertex has indegree ≤ 2
- `thetaP1_indeg_one_iff_pm2`: ±2 are the only affine vertices of indegree 1
- `thetaP1_image_card`: |Im(θ : P¹ → P¹)| = (q + 3) / 2
- `two_cycle_iff`: Clean iff characterization of 2-cycles
-/

noncomputable section

open Finset

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-! ## The projective line as Option K -/

/-- The projective theta map on P¹(K) = Option K.
  none = ∞. θ(∞) = ∞, θ(0) = ∞, θ(x) = some(x + x⁻¹) for x ≠ 0. -/
def thetaP1 (x : Option K) : Option K :=
  match x with
  | none => none
  | some x => if x = 0 then none else some (theta x)

@[simp] theorem thetaP1_none : thetaP1 (none : Option K) = none := rfl

@[simp] theorem thetaP1_zero : thetaP1 (some (0 : K)) = (none : Option K) := by
  simp [thetaP1]

theorem thetaP1_some {x : K} (hx : x ≠ 0) :
    thetaP1 (some x : Option K) = some (theta x) := by
  simp [thetaP1, hx]

/-! ## Projective fiber above infinity -/

/-- The fiber of θ above ∞ (= none) on P¹ is exactly {some 0, none}. -/
theorem thetaP1_eq_none_iff (x : Option K) :
    thetaP1 x = none ↔ x = some 0 ∨ x = none := by
  cases x with
  | none => simp [thetaP1]
  | some x =>
    simp only [thetaP1, Option.some_ne_none]
    split_ifs with h
    · simp [h]
    · simp [h]

/-- For nonzero affine x, θ(x) is affine (not ∞). -/
theorem thetaP1_some_ne_none {x : K} (hx : x ≠ 0) :
    thetaP1 (some x : Option K) ≠ none := by
  simp [thetaP1, hx]

/-! ## Projective fiber above affine elements -/

/-- For a ∈ K, the preimage of some(a) under θ on P¹ consists exactly of the nonzero
solutions t to t² - at + 1 = 0, embedded as some(t). -/
theorem thetaP1_eq_some_iff (x : Option K) (a : K) :
    thetaP1 x = some a ↔ ∃ t : K, t ≠ 0 ∧ t ^ 2 - a * t + 1 = 0 ∧ x = some t := by
  cases x with
  | none => simp [thetaP1]
  | some x =>
    constructor
    · intro h
      have hx : x ≠ 0 := by intro hx; simp [thetaP1, hx] at h
      simp [thetaP1, hx] at h
      exact ⟨x, hx, (theta_eq_iff hx).mp h, rfl⟩
    · rintro ⟨t, ht, heq, hxt⟩
      cases Option.some.inj hxt
      simp [thetaP1, ht]
      exact (theta_eq_iff ht).mpr heq

/-! ## Projective indegree of infinity -/

/-- The indegree of ∞ on P¹ is 2 (preimages are 0 and ∞). -/
theorem thetaP1_indeg_inf :
    (Finset.univ.filter (fun x : Option K => thetaP1 x = none)).card = 2 := by
  convert Set.ncard_eq_two.2 ?_
  any_goals exact { x : Option K | thetaP1 x = none }
  · rw [Set.ncard_eq_toFinset_card']; aesop
  · exact ⟨some 0, none, by simp, by ext; simp [thetaP1_eq_none_iff]⟩

/-! ## Two-cycle existence criterion -/

/-- **Two-cycle existence**: For x ≠ 0 in a field of odd characteristic with θ(x) ≠ 0,
θ(θ(x)) = x with θ(x) ≠ x if and only if x² + 1 = 0 or 2x² + 1 = 0.

Note: if x² + 1 = 0 then θ(x) = 0, contradicting the hypothesis, so in practice
the criterion reduces to 2x² + 1 = 0. -/
theorem two_cycle_iff {x : K} (hx : x ≠ 0) (hθx : theta x ≠ 0)
    (hodd : ringChar K ≠ 2) :
    (theta (theta x) = x ∧ theta x ≠ x) ↔
    (x ^ 2 + 1 = 0 ∨ 2 * x ^ 2 + 1 = 0) := by
  unfold theta at *; simp_all +decide [pow_succ']
  grind

/-! ## Projective image-size formula -/

/-- The image of θ on P¹(F_q) as a Finset. -/
def thetaP1Image (K : Type*) [Field K] [Fintype K] [DecidableEq K] : Finset (Option K) :=
  Finset.univ.image thetaP1

/-- **Projective image-size formula**: |Im(θ : P¹(F_q) → P¹(F_q))| = (q + 3) / 2.

The projective image is the affine image (of size (q+1)/2) plus {∞}, giving (q+3)/2. -/
theorem thetaP1_image_card (hodd : ringChar K ≠ 2) :
    (thetaP1Image K).card = (Fintype.card K + 3) / 2 := by
  have h_image : thetaP1Image K = (thetaImage' K).image some ∪ {none} := by
    unfold thetaP1Image thetaImage'
    ext x
    cases x <;> simp +decide [Fstar']
    · exact ⟨none, rfl⟩
    · constructor
      · rintro ⟨a, ha⟩; rcases a with (_ | a) <;> simp_all +decide [thetaP1]
        exact ⟨a, ha⟩
      · rintro ⟨a, ha, rfl⟩; use some a; simp +decide [ha, thetaP1]
  rw [h_image, Finset.card_union_of_disjoint] <;>
    norm_num [Finset.card_image_of_injective, Function.Injective]
  · rw [theta_image_card hodd]; omega
  · aesop

/-! ## Indegree classification on P¹ -/

/-
PROBLEM
Every vertex of P¹ has indegree at most 2 under θ.

PROVIDED SOLUTION
Case split on y. If y = none, use thetaP1_indeg_inf to get card = 2, hence ≤ 2. If y = some a, the preimages in Option K are: none maps to none ≠ some a, some 0 maps to none ≠ some a, and some t for t ≠ 0 maps to some(theta t). So the filter set injects into {t : K | t ≠ 0 ∧ theta t = a}, which by theta_eq_iff corresponds to roots of the degree-2 polynomial t²-at+1. A degree 2 polynomial has at most 2 roots. Use Polynomial.card_roots_le_degree or similar.
-/
theorem thetaP1_indeg_le_two (y : Option K) :
    (Finset.univ.filter (fun x : Option K => thetaP1 x = y)).card ≤ 2 := by
  by_cases hy : y = none <;> simp +decide [ Finset.card_le_one_iff, Finset.card_le_one, * ] at *; (
  convert thetaP1_indeg_inf.le using 1);
  rcases y with ( _ | ⟨ y ⟩ ) <;> simp_all +decide [ thetaP1 ] ; (
  -- The set of $x$ such that $\theta(x) = y$ is exactly the set of roots of the polynomial $t^2 - yt + 1$.
  have h_roots : Finset.filter (fun x : Option K => thetaP1 x = some y) Finset.univ ⊆ Finset.image (fun t : K => some t) (Multiset.toFinset (Polynomial.roots (Polynomial.X^2 - Polynomial.C y * Polynomial.X + 1))) := by
    intro x hx; simp_all +decide [ Finset.subset_iff ] ;
    rcases x with ( _ | ⟨ x ⟩ ) <;> simp_all +decide [ thetaP1 ];
    exact ⟨ by exact ne_of_apply_ne ( Polynomial.eval 0 ) ( by simp +decide ), by rw [ ← hx.2 ] ; ring_nf; simp +decide [ hx.1 ] ⟩;
  -- The polynomial $t^2 - yt + 1$ has at most 2 roots in $K$.
  have h_poly_roots : (Multiset.toFinset (Polynomial.roots (Polynomial.X^2 - Polynomial.C y * Polynomial.X + 1))).card ≤ 2 := by
    exact le_trans ( Multiset.toFinset_card_le _ ) ( le_trans ( Polynomial.card_roots' _ ) ( by erw [ Polynomial.natDegree_add_C ] ; erw [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> by_cases hy : y = 0 <;> simp +decide [ hy ] ) );
  exact le_trans ( Finset.card_le_card h_roots ) ( Finset.card_image_le.trans h_poly_roots ) |> le_trans ( by rfl ) ;)

/-- ±2 are the only affine vertices of indegree 1 on P¹. -/
theorem thetaP1_indeg_one_iff_pm2 (hodd : ringChar K ≠ 2) (a : K) :
    (Finset.univ.filter (fun x : Option K => thetaP1 x = some a)).card = 1 ↔
    a = 2 ∨ a = -2 := by
  convert indeg_one_iff hodd a using 1
  rw [show ({x : Option K | thetaP1 x = some a} : Finset (Option K)) =
      Finset.image (fun t : K => some t)
        (Finset.filter (fun t : K => theta t = a) (Fstar' K)) from ?_]
  · rw [Finset.card_image_of_injective _ fun x y hxy => by simpa using hxy]
  · ext (_ | x) <;> simp +decide [thetaP1]
    unfold Fstar'; aesop

end