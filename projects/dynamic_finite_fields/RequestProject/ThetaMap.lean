import Mathlib

/-!
# The Exact Fiber Structure of x + 1/x over Finite Fields

We formalize the "proven core" of the analysis of the rational map
  θ(x) = x + x⁻¹
on P¹(F_q), where q is an odd prime power.

## Main results

### Basic properties (any field)
- `theta_inv`: θ(x⁻¹) = θ(x)
- `theta_one`: θ(1) = 2
- `theta_neg_one`: θ(-1) = -2
- `theta_eq_iff`: The fiber law — θ(t) = a iff t² - a·t + 1 = 0 (for t ≠ 0)
- `theta_eq_theta_iff`: θ(x) = θ(y) iff y = x or y = x⁻¹ (for x, y ≠ 0)
- `theta_no_affine_fixed_point`: θ(x) ≠ x for all x ≠ 0

### Cycle constraints (any field)
- `two_cycle_poly`: If θ(θ(x)) = x, θ(x) ≠ 0, x ≠ 0, then (2x²+1)(x²+1) = 0

### Finite field results (odd characteristic)
- `theta_image_card`: |θ(F_q*)| = (q + 1) / 2
- `indeg_zero_count`: Exactly (q - 1)/2 affine elements have indegree 0
- `indeg_one_iff`: The only affine elements of indegree 1 are ±2
- `indeg_two_iff_square`: Indegree 2 ↔ discriminant a² - 4 is a nonzero square
-/

noncomputable section

open Finset

variable {F : Type*} [Field F]

/-- The theta map θ(x) = x + x⁻¹ on a field. -/
def theta (x : F) : F := x + x⁻¹

/-! ## Basic properties -/

@[simp]
theorem theta_def (x : F) : theta x = x + x⁻¹ := rfl

/-- θ is invariant under inversion: θ(x⁻¹) = θ(x). -/
theorem theta_inv (x : F) : theta x⁻¹ = theta x := by
  unfold theta; rw [inv_inv]; ring

/-- θ(1) = 2. -/
theorem theta_one : theta (1 : F) = 2 := by unfold theta; simp; ring

/-- θ(-1) = -2. -/
theorem theta_neg_one : theta (-1 : F) = -2 := by unfold theta; simp; ring

/-! ## The Fiber Law -/

/-- **Fiber law**: For t ≠ 0, θ(t) = a if and only if t² - a·t + 1 = 0. -/
theorem theta_eq_iff {t a : F} (ht : t ≠ 0) :
    theta t = a ↔ t ^ 2 - a * t + 1 = 0 := by
  rw [← eq_comm, mul_comm]
  rw [show theta t = t + t⁻¹ from rfl]
  constructor <;> intro h <;> cases' eq_or_ne t 0 with h0 h0 <;>
    simp_all +decide [sq, sub_eq_zero]
  ring_nf at *; aesop
  grind

/-! ## Fiber characterization -/

/-- For nonzero x and y, θ(x) = θ(y) if and only if y = x or y = x⁻¹. -/
theorem theta_eq_theta_iff {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    theta x = theta y ↔ y = x ∨ y = x⁻¹ := by
  simp_all +decide [theta, eq_comm]
  grind

/-! ## No affine fixed points -/

/-- θ has no affine fixed point: for x ≠ 0, θ(x) ≠ x.
This follows from x⁻¹ = 0 being impossible for x ≠ 0. -/
theorem theta_no_affine_fixed_point {x : F} (hx : x ≠ 0) :
    theta x ≠ x := by
  simp +decide [hx, theta]

/-! ## Critical points and branch values -/

/-- The discriminant of the fiber polynomial t² - a·t + 1 is a² - 4. -/
theorem fiber_discriminant (a : F) :
    (a ^ 2 - 4 : F) = (a - 2) * (a + 2) := by ring

/-! ## 2-cycle constraint -/

/-- **2-cycle polynomial constraint**: If x ≠ 0, θ(x) ≠ 0, and θ(θ(x)) = x,
then (2x² + 1)(x² + 1) = 0. Thus genuine 2-cycles can only come from
x² = -1/2 (when char ≠ 2) or x² = -1. -/
theorem two_cycle_poly {x : F} (hx : x ≠ 0) (hθx : theta x ≠ 0)
    (h : theta (theta x) = x) :
    (2 * x ^ 2 + 1) * (x ^ 2 + 1) = 0 := by
  unfold theta at *
  simp_all +decide [pow_succ, mul_add, mul_assoc, mul_left_comm, add_assoc]
  grind +ring

/-! ## Image-size formulas for finite fields -/

section FiniteField

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- In a field of odd characteristic, 2 ≠ 0. -/
theorem two_ne_zero_of_ringChar_ne_two (hodd : ringChar K ≠ 2) : (2 : K) ≠ 0 := by
  intro h; apply hodd
  have h2 : ringChar K ∣ 2 := (ringChar.spec K 2).mp (by exact_mod_cast h)
  have hp := CharP.char_is_prime_or_zero K (ringChar K)
  rcases hp with hp | hp
  · exact Nat.le_antisymm (Nat.le_of_dvd (by omega) h2) hp.two_le
  · simp [hp] at h2

/-- In a field of odd characteristic, 1 ≠ -1. -/
theorem one_ne_neg_one_of_ringChar_ne_two (hodd : ringChar K ≠ 2) : (1 : K) ≠ -1 := by
  intro h
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_ringChar_ne_two hodd
  apply h2
  have := congr_arg (· + 1) h
  simp at this
  exact_mod_cast this

/-- The set of nonzero elements of K. -/
def Fstar' (K : Type*) [Field K] [Fintype K] [DecidableEq K] : Finset K :=
  Finset.univ.filter (· ≠ 0)

theorem Fstar'_card : (Fstar' K).card = Fintype.card K - 1 := by
  convert Finset.card_erase_of_mem (Finset.mem_univ (0 : K)) using 1
  exact congr_arg Finset.card (by ext; simp +decide [Fstar'])

/-- The image of θ on K* as a Finset. -/
def thetaImage' (K : Type*) [Field K] [Fintype K] [DecidableEq K] : Finset K :=
  (Fstar' K).image theta

set_option maxHeartbeats 800000 in
/-- **Image-size formula**: The image of θ on K* has cardinality (q + 1) / 2 for odd q.

The map θ is generically 2-to-1 on K* (since θ(x) = θ(x⁻¹) and x ≠ x⁻¹ for x ∉ {±1}),
with two exceptional fibers {1} → 2 and {-1} → -2 of size 1 each. -/
theorem theta_image_card (hodd : ringChar K ≠ 2) :
    (thetaImage' K).card = (Fintype.card K + 1) / 2 := by
  have h_fibers : ∀ a ∈ thetaImage' K, (Finset.card (Finset.filter (fun x => theta x = a)
      (Fstar' K))) = if a = 2 ∨ a = -2 then 1 else 2 := by
    intro a ha; split_ifs <;> simp_all +decide [Finset.ext_iff]
    · rcases ‹_› with (rfl | rfl) <;> simp_all +decide [Fstar', Finset.card_eq_one]
      · use 1; grind
      · use -1; ext; simp [theta]; grind
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      refine' Finset.card_eq_two.mpr ⟨x, x⁻¹, _, _⟩ <;> simp_all +decide [Fstar']
      · grind
      · grind
  have h_total_fibers : ∑ a ∈ thetaImage' K, (Finset.card (Finset.filter (fun x => theta x = a)
      (Fstar' K))) = Fintype.card K - 1 := by
    rw [← Finset.card_eq_sum_card_fiberwise]
    · exact Fstar'_card
    · exact fun x hx => Finset.mem_image_of_mem _ hx
  simp_all +decide [Finset.sum_ite]
  have h_simplify : (Finset.card (Finset.filter (fun x => x = 2 ∨ x = -2)
      (thetaImage' K))) = 2 := by
    rw [Finset.card_eq_two]
    refine' ⟨2, -2, _, _⟩ <;> norm_num [Finset.ext_iff]
    · rw [eq_neg_iff_add_eq_zero]; norm_num [two_ne_zero_of_ringChar_ne_two hodd]
      intro h; have := ringChar.spec K; simp_all +decide [show (4 : K) = 2 * 2 by norm_num]
      specialize this 2; simp_all +decide [Nat.dvd_prime]
      exact not_subsingleton _ this
    · exact ⟨Finset.mem_image.mpr ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by norm_num⟩,
        by norm_num [theta]⟩, Finset.mem_image.mpr ⟨-1, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by norm_num⟩, by norm_num [theta]⟩⟩
  rw [show #(thetaImage' K) = #(Finset.filter (fun x => x = 2 ∨ x = -2) (thetaImage' K)) +
      #(Finset.filter (fun x => ¬x = 2 ∧ ¬x = -2) (thetaImage' K)) from ?_]
  · grind
  · rw [Finset.card_filter, Finset.card_filter]
    simpa only [← Finset.sum_add_distrib] using Finset.card_eq_sum_ones _ ▸ by
      congr; ext; by_cases h2 : ‹K› = 2 <;> by_cases h3 : ‹K› = -2 <;> simp +decide [h2, h3]

/-- Exactly (q - 1)/2 affine elements have no affine preimage under θ.

These are exactly the elements a ∈ F_q for which a² - 4 is a nonsquare. -/
theorem indeg_zero_count (hodd : ringChar K ≠ 2) :
    (Finset.univ.filter (fun a : K => ∀ t : K, t ≠ 0 → theta t ≠ a)).card =
    (Fintype.card K - 1) / 2 := by
  convert congr_arg (fun x : ℕ => Fintype.card K - x) (theta_image_card hodd) using 1
  · rw [show (Finset.univ.filter fun a => ∀ t : K, t ≠ 0 → theta t ≠ a) =
        Finset.univ \ (Finset.image theta (Finset.univ.filter (· ≠ 0))) from ?_,
        Finset.card_sdiff] <;> norm_num
    · rfl
    · ext; simp [theta]
  · have h_card : Fintype.card K % 2 = 1 := by
      have := FiniteField.card K (ringChar K)
      exact this.elim fun n hn => hn.2.symm ▸ Nat.odd_iff.mp (Odd.pow (hn.1.odd_of_ne_two hodd))
    omega

/-- The only affine elements of indegree 1 are 2 and -2 (the branch values of θ).

These correspond to the critical points ±1, where the fiber polynomial t² - at + 1
has a double root. -/
theorem indeg_one_iff (hodd : ringChar K ≠ 2) (a : K) :
    ((Fstar' K).filter (fun t => theta t = a)).card = 1 ↔ a = 2 ∨ a = -2 := by
  constructor
  · intro h_card
    obtain ⟨t, ht⟩ : ∃ t ∈ Fstar' K, theta t = a ∧
        ∀ t' ∈ Fstar' K, theta t' = a → t' = t := by
      rw [Finset.card_eq_one] at h_card
      obtain ⟨t, ht⟩ := h_card; use t; simp_all +decide [Finset.eq_singleton_iff_unique_mem]
    have h_inv : t⁻¹ ∈ Fstar' K ∧ theta t⁻¹ = a := by
      simp_all +decide [Fstar', theta]
      rw [add_comm, ht.2.1]
    have h_inv_eq : t⁻¹ = t := ht.2.2 _ h_inv.1 h_inv.2
    rw [inv_eq_one_div, div_eq_iff] at h_inv_eq <;> norm_num at *
    · rcases mul_self_eq_one_iff.mp h_inv_eq.symm with (rfl | rfl) <;>
        norm_num [← ht.2.1] at *
    · exact Finset.mem_filter.mp ht.1 |>.2
  · rintro (rfl | rfl) <;> simp +decide [theta_one]
    · exact Finset.card_eq_one.mpr ⟨1, by ext t; simp [Fstar']; grind⟩
    · exact Finset.card_eq_one.mpr ⟨-1, by ext t; simp [Fstar']; grind⟩

/-- An affine element has indegree 2 iff its fiber discriminant a² - 4 is a nonzero square.

When a² - 4 is a nonzero square s², the two preimages are (a ± s)/2, which are
reciprocal to each other. -/
theorem indeg_two_iff_square (hodd : ringChar K ≠ 2) (a : K) :
    ((Fstar' K).filter (fun t => theta t = a)).card = 2 ↔
    (∃ s : K, s ≠ 0 ∧ s ^ 2 = a ^ 2 - 4) := by
  refine' ⟨fun h => _, fun ⟨s, hs, hs'⟩ => _⟩
  · obtain ⟨t, ht, u, hu, htu⟩ := Finset.one_lt_card.1 (by linarith)
    use t - u
    simp_all +decide [sub_eq_iff_eq_add, Fstar']
    grind +ring
  · set t1 := (a + s) / 2
    set t2 := (a - s) / 2
    have h_distinct : t1 ≠ t2 := by
      have : (2 : K) ≠ 0 := two_ne_zero_of_ringChar_ne_two hodd
      grind
    have h_nonzero : t1 ≠ 0 ∧ t2 ≠ 0 := by
      constructor <;> intro h <;> simp_all +decide [sub_eq_iff_eq_add]
      · grind
      · grind
    have h_theta : theta t1 = a ∧ theta t2 = a := by
      simp +zetaDelta at *
      grind
    refine' Finset.card_eq_two.mpr ⟨t1, t2, _, _⟩ <;> simp_all +decide [Finset.ext_iff]
    intro x; constructor <;> intro hx <;> simp_all +decide [Fstar']
    · grind
    · grind

end FiniteField

end
