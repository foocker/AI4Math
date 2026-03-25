import Mathlib
import RequestProject.ThetaMap
import RequestProject.ThetaCycles

/-!
# Four-Cycle Cyclotomic Helpers

Infrastructure for proving the four-cycle count formula:
  N₄ = 𝟙[q ≡ 1 mod 16] + 2·𝟙[q ≡ 1 mod 60]

This file provides the cyclotomic criteria for the quartic factor
2x⁴+4x²+1 (related to primitive 16th roots) and the octic factor
x⁸+7x⁶+14x⁴+8x²+1 (related to primitive 60th roots).

## Strategy

The proofs mirror the m₃₆ approach in ThetaCycles.lean:
1. Chebyshev identities connecting polynomial roots to roots of unity
2. Backward direction: q ≡ 1 mod n → polynomial has roots
3. Forward direction: polynomial has roots → q ≡ ±1 mod n
4. Elimination of -1 case using q ≡ 1 mod 4
-/

noncomputable section

open Finset Polynomial

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-! ## Part 1: m₁₆ criteria (quartic factor 2x⁴+4x²+1)

m₁₆(u) = u⁴ - 4u² + 2 is the minimal polynomial of 2cos(π/8) over ℚ.
Key identity: ζ⁴ · m₁₆(ζ+ζ⁻¹) = ζ⁸ + 1.
So if ζ²-uζ+1=0 and m₁₆(u)=0, then ζ⁸ = -1, hence IsPrimitiveRoot ζ 16.
-/

/-
PROBLEM
Chebyshev identity for m₁₆: ζ⁴·(u⁴-4u²+2) = ζ⁸+1 when u = ζ+ζ⁻¹.
    This is the ring identity that connects m₁₆ roots to 16th roots of unity.
    Proof: from ζ²-uζ+1=0 we get u = ζ+ζ⁻¹, and
    ζ⁴·((ζ+ζ⁻¹)⁴ - 4(ζ+ζ⁻¹)² + 2) = ζ⁸+1 by field_simp+ring.

PROVIDED SOLUTION
From ζ²-uζ+1=0, we get ζ² = uζ-1. We can express ζ⁸ in terms of u and ζ using repeated substitution:
ζ² = uζ-1
ζ⁴ = (ζ²)² = (uζ-1)² = u²ζ²-2uζ+1 = u²(uζ-1)-2uζ+1 = (u³-2u)ζ-(u²-1)
ζ⁸ = (ζ⁴)² = ((u³-2u)ζ-(u²-1))² = (u³-2u)²ζ²-2(u³-2u)(u²-1)ζ+(u²-1)²
  = (u³-2u)²(uζ-1)-2(u³-2u)(u²-1)ζ+(u²-1)²
  = [(u³-2u)²u - 2(u³-2u)(u²-1)]ζ + [-(u³-2u)² + (u²-1)²]
  = (u⁷-6u⁵+10u³-4u)ζ + (-u⁶+5u⁴-6u²+1)

So ζ⁸+1 = (u⁷-6u⁵+10u³-4u)ζ + (-u⁶+5u⁴-6u²+2)

On the other hand:
ζ⁴·(u⁴-4u²+2) = [(u³-2u)ζ-(u²-1)]·(u⁴-4u²+2)
  = (u³-2u)(u⁴-4u²+2)ζ - (u²-1)(u⁴-4u²+2)
  = (u⁷-6u⁵+10u³-4u)ζ + (-u⁶+5u⁴-6u²+2)

These match! So ζ⁸+1 = ζ⁴·(u⁴-4u²+2) = ζ⁴·0 = 0 (since hm16 gives u⁴-4u²+2=0).

Proof strategy: Use linear_combination or express ζ⁸+1 as ζ⁴·(u⁴-4u²+2) plus a multiple of (ζ²-uζ+1). Concretely:
ζ⁸+1 - ζ⁴·(u⁴-4u²+2) should be a polynomial in ζ,u that's divisible by (ζ²-uζ+1).

Actually, the cleanest approach:
have hζne : ζ ≠ 0 (from hquad: if ζ=0 then 1=0)
have hsum : ζ + ζ⁻¹ = u (from hquad, rearranging)
Then: ζ⁴ · ((ζ+ζ⁻¹)⁴-4(ζ+ζ⁻¹)²+2) = ζ⁸+1 (by field_simp; ring)
Since (ζ+ζ⁻¹)⁴-4(ζ+ζ⁻¹)²+2 = u⁴-4u²+2 = 0 (by hm16), we get ζ⁸+1 = 0.

Use `have hζne : ζ ≠ 0` from hquad, `have hsum : ζ + ζ⁻¹ = u` from hquad, then show `ζ ^ 4 * (u ^ 4 - 4 * u ^ 2 + 2) = ζ ^ 8 + 1` by rw [← hsum] and field_simp; ring, then rw [hm16, mul_zero].
-/
lemma root_quad_gives_pow8_eq_neg_one {R : Type*} [Field R]
    {u ζ : R} (hquad : ζ ^ 2 - u * ζ + 1 = 0) (hm16 : u ^ 4 - 4 * u ^ 2 + 2 = 0) :
    ζ ^ 8 + 1 = 0 := by
  grind

/-
PROBLEM
If ζ²-uζ+1=0 and m₁₆(u)=0 in char ≠ 2, then ζ is a primitive 16th root of unity.
    Proof: from the Chebyshev identity, ζ⁸=-1, so ζ¹⁶=1 and ζ⁸≠1 (char≠2),
    giving orderOf ζ = 16.

PROVIDED SOLUTION
From root_quad_gives_pow8_eq_neg_one: ζ⁸+1=0, so ζ⁸=-1.
Then ζ¹⁶ = (ζ⁸)² = 1. And ζ⁸≠1 (since ζ⁸=-1 and char≠2, so -1≠1).
So orderOf ζ | 16 and orderOf ζ ∤ 8.
The divisors of 16 are 1,2,4,8,16. Since orderOf ∤ 8 rules out 1,2,4,8, we get orderOf ζ = 16.

Steps:
1. have h8 := root_quad_gives_pow8_eq_neg_one hquad hm16 (gives ζ⁸+1=0)
2. have hζ8 : ζ^8 = -1 := by linear_combination -h8
3. have h16 : ζ^16 = 1 := by calc ζ^16 = (ζ^8)^2 := by ring; _ = 1 := by rw [hζ8]; ring
4. have h8ne : ζ^8 ≠ 1 (from hζ8 and char≠2)
5. Use orderOf_dvd_of_pow_eq_one and orderOf_dvd_iff_pow_eq_one to conclude orderOf = 16
6. IsPrimitiveRoot.iff_orderOf.mpr
-/
lemma isPrimitiveRoot_of_quad_m16_root {R : Type*} [Field R]
    (hchar2 : ringChar R ≠ 2)
    {u ζ : R} (hquad : ζ ^ 2 - u * ζ + 1 = 0) (hm16 : u ^ 4 - 4 * u ^ 2 + 2 = 0) :
    IsPrimitiveRoot ζ 16 := by
  refine' ⟨ _, _ ⟩;
  · grind +locals;
  · intro l hl
    have h_order : orderOf ζ = 16 := by
      have h8 : ζ ^ 8 = -1 := by
        grind +revert
      have h16 : ζ ^ 16 = 1 := by
        linear_combination' h8 * h8
      have h8ne : ζ ^ 8 ≠ 1 := by
        grind +suggestions
      have h_order : orderOf ζ ∣ 16 ∧ ¬orderOf ζ ∣ 8 := by
        simp_all +decide [ orderOf_dvd_iff_pow_eq_one ]
      have h_order_eq : orderOf ζ = 16 := by
        have := Nat.le_of_dvd ( by decide ) h_order.1; interval_cases orderOf ζ <;> simp +decide at h_order ⊢;
      exact h_order_eq;
    exact h_order ▸ orderOf_dvd_iff_pow_eq_one.mpr hl

/-
PROBLEM
A primitive 16th root gives a root of m₁₆ via Chebyshev.
    If ζ is a primitive 16th root, then u=ζ+ζ⁻¹ satisfies u⁴-4u²+2=0.
    Proof: ζ⁸=-1 (from IsPrimitiveRoot 16), then
    ζ⁴·m₁₆(ζ+ζ⁻¹) = ζ⁸+1 = 0, and ζ⁴≠0.

PROVIDED SOLUTION
Proof follows the same pattern as `isPrimitiveRoot_36_implies_m36_root`:
1. ζ is a primitive 16th root, so ζ⁸ is a primitive 2nd root, i.e., ζ⁸ = -1 (since ζ⁸ ≠ 1 because orderOf ζ = 16).
   Actually more directly: ζ¹⁶ = 1 and ζ⁸ ≠ 1 (since 8 < 16 = orderOf ζ).
   Then (ζ⁸)² = ζ¹⁶ = 1 and ζ⁸ ≠ 1, so ζ⁸ = -1, i.e., ζ⁸+1=0.
2. ζ ≠ 0 (since ζ has finite order > 0).
3. ζ⁴ ≠ 0 (since ζ ≠ 0).
4. ζ⁴ · m₁₆(ζ+ζ⁻¹) = ζ⁸+1 (by field_simp; ring).
5. Since ζ⁸+1=0 and ζ⁴≠0, we get m₁₆(ζ+ζ⁻¹)=0.

Key steps:
- Get ζ⁸ = -1: use hζ.pow_eq_one to get ζ¹⁶=1, then show ζ⁸≠1 using IsPrimitiveRoot properties (ζ⁸ has order 2, or use that orderOf ζ = 16 so ¬(orderOf ζ ∣ 8)), so ζ⁸=-1 since (ζ⁸)²=1.
- Show the ring identity and conclude.
-/
lemma isPrimitiveRoot_16_implies_m16_root {ζ : K} (hζ : IsPrimitiveRoot ζ 16) :
    (ζ + ζ⁻¹) ^ 4 - 4 * (ζ + ζ⁻¹) ^ 2 + 2 = 0 := by
  have hζ_pow : ζ ^ 8 = -1 := by
    have hζ_pow : ζ ^ 16 = 1 := by
      exact hζ.pow_eq_one
    have hζ_neg_one : ζ ^ 8 ≠ 1 := by
      exact fun h => by have := hζ.pow_eq_one_iff_dvd 8; simp_all +decide ;
    have hζ_sq : (ζ ^ 8) ^ 2 = 1 := by
      linear_combination' hζ_pow
    have hζ_neg_one : ζ ^ 8 = -1 := by
      exact Or.resolve_left ( sq_eq_one_iff.mp hζ_sq ) hζ_neg_one
    exact hζ_neg_one;
  grind +ring

/-
PROBLEM
Backward: if q ≡ 1 mod 16, then m₁₆ has a root in K.

PROVIDED SOLUTION
Identical pattern to m36_root_of_mod36:
1. hmod gives 16 | (q-1).
2. Fintype.card Kˣ = q-1, so 16 | |Kˣ|.
3. Kˣ is cyclic (IsCyclic instance for finite field units).
4. By IsCyclic.card_orderOf_eq_totient, there exist elements of order 16. Pick one: g with orderOf g = 16.
5. g is a primitive 16th root: IsPrimitiveRoot (g : K) 16.
6. By isPrimitiveRoot_16_implies_m16_root, u = (g : K) + (g : K)⁻¹ satisfies m₁₆(u)=0.

Use the same code pattern as m36_root_of_mod36 in ThetaCycles.lean.
-/
lemma m16_root_of_mod16 (hmod : Fintype.card K % 16 = 1) :
    ∃ u : K, u ^ 4 - 4 * u ^ 2 + 2 = 0 := by
  obtain ⟨g, hg⟩ : ∃ g : Kˣ, orderOf g = 16 := by
    have h_div : 16 ∣ (Fintype.card Kˣ) := by
      rw [ Fintype.card_units ] ; omega;
    obtain ⟨ g, hg ⟩ := IsCyclic.exists_generator ( α := Kˣ );
    obtain ⟨ k, hk ⟩ := h_div; use g ^ ( Fintype.card Kˣ / 16 ) ; rw [ orderOf_pow' ] <;> simp +decide [ hk, orderOf_eq_card_of_forall_mem_zpowers hg ] ;
    · rw [ Nat.mul_div_cancel _ ( Nat.pos_of_ne_zero ( by rintro rfl; simp_all +decide [ Fintype.card_eq_zero_iff ] ) ) ];
    · linarith [ show Fintype.card Kˣ > 0 from Fintype.card_pos ];
  have hprim : IsPrimitiveRoot (g : K) 16 := by
    convert IsPrimitiveRoot.coe_units_iff.mpr ( IsPrimitiveRoot.iff_orderOf.mpr hg );
  exact ⟨ ( g : K ) + ( g : K ) ⁻¹, isPrimitiveRoot_16_implies_m16_root hprim ⟩

/-- q ≡ 1 mod 4 and q ≡ -1 mod 16 is impossible. -/
lemma not_neg_one_mod_16_of_one_mod_4 {q : ℕ}
    (h4 : q % 4 = 1) (h16 : q % 16 = 15) : False := by
  omega

/-
PROBLEM
Forward direction for m₁₆ when the quadratic X²-uX+1 has a root in K.
    If ζ ∈ K satisfies ζ²-uζ+1=0 and m₁₆(u)=0, then orderOf ζ = 16
    and 16 | q-1, so q ≡ 1 mod 16.

PROVIDED SOLUTION
If ζ ∈ K satisfies ζ²-uζ+1=0 and m₁₆(u)=0, then by isPrimitiveRoot_of_quad_m16_root, IsPrimitiveRoot ζ 16.
So orderOf ζ = 16. Since ζ ∈ K*, orderOf ζ | |K*| = q-1. So 16 | q-1, i.e., q ≡ 1 mod 16.

Steps:
1. have hprim := isPrimitiveRoot_of_quad_m16_root hchar2 hquad hm16
2. have hord : orderOf ζ = 16 := IsPrimitiveRoot.iff_orderOf.mp hprim
3. have ζ ≠ 0 (from hquad)
4. set ζu := Units.mk0 ζ (ne_zero)
5. have orderOf ζu = 16 (transfer from ζ)
6. have 16 ∣ Fintype.card Kˣ := hord ▸ orderOf_dvd_card
7. rw [Fintype.card_units]; omega
-/
lemma mod16_of_quad_root_in_K (hchar2 : ringChar K ≠ 2)
    {u : K} (hm16 : u ^ 4 - 4 * u ^ 2 + 2 = 0)
    {ζ : K} (hquad : ζ ^ 2 - u * ζ + 1 = 0) :
    Fintype.card K % 16 = 1 := by
  by_contra h_contra
  have h_order : IsPrimitiveRoot ζ 16 := by
    apply isPrimitiveRoot_of_quad_m16_root hchar2 hquad hm16;
  have h_div : 16 ∣ (Fintype.card K - 1) := by
    exact h_order.2 _ ( by rw [ ← FiniteField.pow_card_sub_one_eq_one ζ ( by aesop ) ] );
  exact h_contra ( by obtain ⟨ k, hk ⟩ := h_div; rw [ tsub_eq_iff_eq_add_of_le ( Nat.succ_le_of_lt ( Fintype.card_pos ) ) ] at hk; norm_num [ Nat.add_mod, hk ] )

/-
PROBLEM
Forward: if m₁₆ has a root in K (with q ≡ 1 mod 4), then q ≡ 1 mod 16.
    Case splits on whether X²-uX+1 has a root in K.

PROVIDED SOLUTION
Same pattern as mod36_of_m36_root. Case split on whether X²-uX+1 has a root in K.

Case 1: ∃ ζ ∈ K with ζ²-uζ+1=0. Then mod16_of_quad_root_in_K gives q ≡ 1 mod 16.

Case 2: X²-uX+1 has no root in K (irreducible quadratic). Build L = AdjoinRoot(X²-uX+1).
The root ζ in L is a primitive 16th root of unity (by isPrimitiveRoot_of_quad_m16_root).
Frobenius maps ζ → ζ^q. Since ζ∉K, ζ^q ≠ ζ.
Both ζ and ζ^q are roots of X²-u_L·X+1=0 (where u_L = algebraMap K L u).
The quadratic has exactly 2 roots: ζ and ζ⁻¹ (product = 1).
Since ζ^q ≠ ζ, we get ζ^q = ζ⁻¹, so ζ^(q+1) = 1, and 16 | q+1, i.e. q ≡ 15 mod 16.
But q ≡ 1 mod 4 (from hsplit), and 15 mod 4 = 3 ≠ 1. Contradiction.

So only Case 1 is possible, giving q ≡ 1 mod 16.

Use the same code pattern as mod36_of_m36_root but with 16 instead of 36, isPrimitiveRoot_of_quad_m16_root instead of isPrimitiveRoot_of_quad_m36_root, and not_neg_one_mod_16_of_one_mod_4 instead of not_neg_one_mod_36_of_one_mod_4.
-/
set_option maxHeartbeats 1600000 in
lemma mod16_of_m16_root (hchar2 : ringChar K ≠ 2)
    (hsplit : ∃ i : K, i ^ 2 = -1)
    (hroot : ∃ u : K, u ^ 4 - 4 * u ^ 2 + 2 = 0) :
    Fintype.card K % 16 = 1 := by
  obtain ⟨ u, hu ⟩ := hroot;
  have h_alg_closed : ∀ f : Polynomial K, f.degree > 0 → ∃ z : AlgebraicClosure K, f.eval₂ (algebraMap K (AlgebraicClosure K)) z = 0 := by
    intro f hf;
    have := @IsAlgClosed.exists_root ( AlgebraicClosure K ) _ _ ( f.map ( algebraMap K ( AlgebraicClosure K ) ) ) ?_ <;> aesop;
  obtain ⟨ ζ, hζ ⟩ := h_alg_closed ( Polynomial.X ^ 2 - Polynomial.C u * Polynomial.X + 1 ) ( by erw [ Polynomial.degree_add_eq_left_of_degree_lt ] <;> erw [ Polynomial.degree_add_eq_left_of_degree_lt ] <;> by_cases hu : u = 0 <;> simp +decide [ hu ] ) ; simp_all +decide [ Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C ] ;
  have hζ_pow : ζ ^ 8 + 1 = 0 := by
    have hζ_8 : (algebraMap K (AlgebraicClosure K)) u ^ 4 - 4 * (algebraMap K (AlgebraicClosure K)) u ^ 2 + 2 = 0 := by
      simpa using congr_arg ( algebraMap K ( AlgebraicClosure K ) ) hu;
    grind;
  have hζ_order : IsPrimitiveRoot ζ 16 := by
    have hζ_order : IsPrimitiveRoot ζ 16 := by
      have hζ_order : ζ ^ 16 = 1 := by
        linear_combination' hζ_pow * ( ζ ^ 8 - 1 )
      have hζ_order : ¬(ζ ^ 8 = 1) := by
        have hζ_order : (2 : AlgebraicClosure K) ≠ 0 := by
          grind +suggestions
        have hζ_order : ζ ^ 8 ≠ 1 := by
          exact fun h => hζ_order <| by linear_combination' hζ_pow - h;
        exact hζ_order
      refine' ⟨ by assumption, fun l hl => _ ⟩;
      rw [ ← orderOf_dvd_iff_pow_eq_one ] at *;
      have := Nat.le_of_dvd ( by decide ) ‹orderOf ζ ∣ 16›; interval_cases orderOf ζ <;> simp_all +decide ;
    exact hζ_order;
  have hζ_pow_q : ζ ^ Fintype.card K = ζ ∨ ζ ^ Fintype.card K = ζ⁻¹ := by
    have hζ_pow_q : (ζ ^ Fintype.card K) ^ 2 - (algebraMap K (AlgebraicClosure K)) u * (ζ ^ Fintype.card K) + 1 = 0 := by
      convert congr_arg ( · ^ Fintype.card K ) hζ using 1 ; ring;
      · haveI := Fact.mk ( show Nat.Prime ( ringChar K ) from ?_ ) ; simp +decide [ ← ZMod.natCast_eq_zero_iff, pow_mul', mul_pow, sub_mul, add_mul, mul_assoc, mul_comm, mul_left_comm ] ; ring;
        · have h_frobenius : ∀ (a b : AlgebraicClosure K), (a + b) ^ Fintype.card K = a ^ Fintype.card K + b ^ Fintype.card K := by
            have h_frobenius : ∀ (a b : AlgebraicClosure K), (a + b) ^ ringChar K = a ^ ringChar K + b ^ ringChar K := by
              simp +decide [ add_pow_char ];
            have h_frobenius_pow : ∀ (n : ℕ) (a b : AlgebraicClosure K), (a + b) ^ (ringChar K ^ n) = a ^ (ringChar K ^ n) + b ^ (ringChar K ^ n) := by
              intro n a b; induction n <;> simp_all +decide [ pow_succ, pow_mul ] ;
            have := FiniteField.card K ( ringChar K ) ; aesop;
          have h_frobenius : ∀ (a b : AlgebraicClosure K), (a - b) ^ Fintype.card K = a ^ Fintype.card K - b ^ Fintype.card K := by
            intro a b; specialize h_frobenius ( a - b ) b; aesop;
          simp_all +decide [ pow_mul', sub_eq_add_neg, add_assoc ];
          rw [ mul_pow, eq_comm ];
          exact congr_arg _ ( by rw [ ← map_pow, FiniteField.pow_card ] );
        · have := FiniteField.card K ( ringChar K ) ; aesop;
      · rw [ zero_pow ( Fintype.card_ne_zero ) ];
    grind;
  cases' hζ_pow_q with h h;
  · have := hζ_order.pow_eq_one_iff_dvd ( Fintype.card K - 1 ) ; simp_all +decide [ Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt ] ;
    rcases n : Fintype.card K with ( _ | _ | n ) <;> simp_all +decide [ pow_succ' ];
    grind +splitIndPred;
  · have hζ_pow_q : ζ ^ (Fintype.card K + 1) = 1 := by
      grind;
    have := hζ_order.2 ( Fintype.card K + 1 ) hζ_pow_q;
    obtain ⟨ k, hk ⟩ := this; have := congr_arg ( · % 4 ) hk; norm_num [ Nat.add_mod, Nat.mul_mod ] at this; have := mod4_of_neg_one_is_square hchar2 hsplit; simp_all +decide ;

/-- m₁₆ existence criterion: m₁₆ has a root in K ↔ q ≡ 1 mod 16
    (given q ≡ 1 mod 4, char ≠ 2). -/
theorem m16_root_iff_mod16 (hchar2 : ringChar K ≠ 2)
    (hsplit : ∃ i : K, i ^ 2 = -1) :
    (∃ u : K, u ^ 4 - 4 * u ^ 2 + 2 = 0) ↔ Fintype.card K % 16 = 1 :=
  ⟨mod16_of_m16_root hchar2 hsplit, m16_root_of_mod16⟩

/-! ## Part 2: m₆₀ criteria (octic factor)

m₆₀(v) = v⁸ - 7v⁶ + 14v⁴ - 8v² + 1 is the minimal polynomial
of 2cos(2π/60) over ℚ.

Key identity: ζ⁸ · m₆₀(ζ+ζ⁻¹) = Φ₆₀(ζ).

The octic factor x⁸+7x⁶+14x⁴+8x²+1 corresponds to m₆₀*(u) = u⁸-8u⁶+14u⁴-7u²+1
(the reciprocal polynomial) via the bridge. Since m₆₀*(u)=0 ↔ m₆₀(1/u)=0 (for u≠0),
the octic has roots iff m₆₀ has roots.
-/

/-
PROBLEM
m₆₀* has a root iff m₆₀ has a root.
    m₆₀*(u) = u⁸·m₆₀(1/u), and both have nonzero constant term.

PROVIDED SOLUTION
m₆₀*(u) = u⁸-8u⁶+14u⁴-7u²+1 and m₆₀(v) = v⁸-7v⁶+14v⁴-8v²+1.
These are reciprocal polynomials: m₆₀*(u) = u⁸·m₆₀(1/u) for u≠0.

Forward: if m₆₀*(u)=0 for some u, then u≠0 (since m₆₀*(0)=1≠0), and v:=1/u satisfies m₆₀(v)=0.
Backward: if m₆₀(v)=0 for some v, then v≠0 (since m₆₀(0)=1≠0), and u:=1/v satisfies m₆₀*(u)=0.

For the forward direction: m₆₀*(u) = 0 and u≠0. Set v = u⁻¹. Then:
v⁸-7v⁶+14v⁴-8v²+1 = u⁻⁸·(1-7u²+14u⁴-8u⁶+u⁸) = u⁻⁸·(u⁸-8u⁶+14u⁴-7u²+1) after noting
u⁸-8u⁶+14u⁴-7u²+1 = 0 gives 1-7u²+14u⁴-8u⁶+u⁸ = ... actually they differ.

Wait: m₆₀*(u) = u⁸-8u⁶+14u⁴-7u²+1. m₆₀(v) = v⁸-7v⁶+14v⁴-8v²+1.
For v = 1/u: v⁸-7v⁶+14v⁴-8v²+1 = (1-7u²+14u⁴-8u⁶+u⁸)/u⁸ = (u⁸-8u⁶+14u⁴-7u²+1)/u⁸
Wait, 1-7u²+14u⁴-8u⁶+u⁸ vs u⁸-8u⁶+14u⁴-7u²+1: these ARE the same! Both equal u⁸-8u⁶+14u⁴-7u²+1? No:
1-7u²+14u⁴-8u⁶+u⁸ = u⁸-8u⁶+14u⁴-7u²+1. Yes they're the same!

So m₆₀(1/u) = (u⁸-8u⁶+14u⁴-7u²+1)/u⁸ = m₆₀*(u)/u⁸.
If m₆₀*(u)=0 then m₆₀(1/u)=0. Since u≠0, set v=1/u.

So the proof is: constructor
· rintro ⟨u, hu⟩; have hune : u ≠ 0 := by intro h; simp [h] at hu; exact one_ne_zero hu
  exact ⟨u⁻¹, by field_simp at hu ⊢; [linarith or ring_nf and use hu]⟩
· rintro ⟨v, hv⟩; have hvne : v ≠ 0 := by intro h; simp [h] at hv; exact one_ne_zero hv
  exact ⟨v⁻¹, by field_simp at hv ⊢; [linarith or ring_nf and use hv]⟩

The key identity: u⁸·m₆₀(u⁻¹) = m₆₀*(u). So if m₆₀*(u)=0 and u≠0, then m₆₀(u⁻¹)=0.
Similarly v⁸·m₆₀*(v⁻¹) = m₆₀(v).
-/
lemma m60star_root_iff_m60_root :
    (∃ u : K, u ^ 8 - 8 * u ^ 6 + 14 * u ^ 4 - 7 * u ^ 2 + 1 = 0) ↔
    (∃ v : K, v ^ 8 - 7 * v ^ 6 + 14 * v ^ 4 - 8 * v ^ 2 + 1 = 0) := by
  refine' ⟨ fun ⟨ u, hu ⟩ => _, fun ⟨ v, hv ⟩ => _ ⟩;
  · use u⁻¹;
    grind;
  · by_cases hv0 : v = 0 <;> simp_all +decide [ pow_succ, mul_assoc ];
    use v⁻¹; field_simp [hv0]; ring; (
    grind +splitIndPred);

/-
PROBLEM
Chebyshev identity: if ζ²-uζ+1=0 and m₆₀(u)=0, then ζ has order 60.
We establish this through the identity ζ⁸·m₆₀(ζ+ζ⁻¹) = Φ₆₀(ζ).

Key identity for m₆₀: if ζ²-uζ+1=0 and m₆₀(u)=0, then ζ³⁰+1=0.
    This is analogous to ζ⁸+1=0 for m₁₆.

PROVIDED SOLUTION
From ζ²-vζ+1=0, we get ζ² = vζ-1 and ζ+ζ⁻¹ = v (since ζ≠0).

We need to show ζ³⁰+1=0.

The key identity is: ζ⁸·m₆₀(ζ+ζ⁻¹) = Φ₆₀(ζ) where Φ₆₀ is the 60th cyclotomic polynomial.

But more directly, we can use the factorization:
ζ³⁰+1 = (ζ²)¹⁵+1. Since ζ²=vζ-1:

Actually, the cleanest approach uses the intermediate identity.
From ζ²=vζ-1, compute ζ⁴, ζ⁸, ζ¹⁶ mod (ζ²-vζ+1):
ζ⁴ = (v³-2v)ζ-(v²-1)
ζ⁸ = (v⁷-6v⁵+10v³-4v)ζ + (-v⁶+5v⁴-6v²+1)

Since we know (from the m₁₆ case) ζ⁸+1 = ζ⁴·(v⁴-4v²+2) (same ring identity with v instead of u), but here m₆₀(v)≠m₁₆(v).

The actual approach: show that ζ³⁰+1 equals some expression times m₆₀(v), so when m₆₀(v)=0, ζ³⁰+1=0.

More precisely, ζ³⁰ mod (ζ²-vζ+1) = a₃₀(v)·ζ + b₃₀(v). We need a₃₀(v) ≡ 0 mod m₆₀(v) and b₃₀(v)+1 ≡ 0 mod m₆₀(v).

Since this is verified computationally (we checked ζ³⁰=-1 for v a root of m₆₀ over F_61), the identity holds. The proof should use the approach: establish ζ⁸·m₆₀(ζ+ζ⁻¹) = Φ₆₀(ζ), show Φ₆₀(ζ) divides ζ⁶⁰-1, and from ζ⁶⁰=(ζ³⁰)², if ζ³⁰≠-1 then...

Actually, the cleanest algebraic proof:
1. have hζne : ζ ≠ 0 (from hquad)
2. have hsum : ζ + ζ⁻¹ = v (from hquad)
3. Show ζ⁸ · (v⁸-7v⁶+14v⁴-8v²+1) = ζ³⁰ + ζ²⁴ - ζ¹⁸ - ζ¹² + ζ⁶ + 1 ... hmm this is complex.

Alternative: just use `grind` or `linear_combination` with the appropriate coefficients. The proof is that ζ³⁰+1 can be written as a polynomial in ζ and v that's divisible by both (ζ²-vζ+1) and m₆₀(v). This is a polynomial identity that should be provable by ring/grind after substituting ζ²=vζ-1 repeatedly.

Actually, the simplest approach for the prover: since this is ultimately a ring identity in ℤ[v,ζ]/(ζ²-vζ+1, m₆₀(v)), just try `grind` or set up the identity using linear_combination.
-/
lemma root_quad_gives_pow30_eq_neg_one {R : Type*} [Field R]
    {v ζ : R} (hquad : ζ ^ 2 - v * ζ + 1 = 0)
    (hm60 : v ^ 8 - 7 * v ^ 6 + 14 * v ^ 4 - 8 * v ^ 2 + 1 = 0) :
    ζ ^ 30 + 1 = 0 := by
  grind +ring

/-
PROBLEM
If ζ²-vζ+1=0 and m₆₀(v)=0 in char ≠ 2, 3, 5, then IsPrimitiveRoot ζ 60.
    From ζ³⁰=-1 we get ζ⁶⁰=1 and ζ³⁰≠1. Need additional divisibility checks
    to ensure orderOf ζ = 60 exactly (not just 60 | 2·orderOf).

PROVIDED SOLUTION
From root_quad_gives_pow30_eq_neg_one: ζ³⁰=-1 (linear_combination).
Then ζ⁶⁰=1 and ζ³⁰≠1 (char≠2).
So orderOf ζ ∣ 60 and ¬(orderOf ζ ∣ 30).

Must show orderOf ζ = 60. Divisors of 60 not dividing 30 are: {4, 12, 20, 60}.

Rule out orderOf = 4: ζ⁴=1. Then ζ³⁰=(ζ⁴)⁷·ζ²=ζ². So ζ²=-1. From ζ²-vζ+1=0: -1-vζ+1=0, vζ=0. Since ζ≠0 (from hquad), v=0. But m₆₀(0)=1≠0. Contradiction with hm60.

Rule out orderOf = 12: ζ¹²=1. Then ζ³⁰=(ζ¹²)²·ζ⁶=ζ⁶. So ζ⁶=-1. From ζ²=vζ-1, compute ζ⁶=(v⁵-4v³+3v)ζ-(v⁴-3v²+1) [using repeated substitution]. If ζ⁶=-1, then (v⁵-4v³+3v)ζ-(v⁴-3v²+1)=-1, giving (v⁵-4v³+3v)ζ=v⁴-3v².
   If v⁵-4v³+3v≠0: ζ=v(v³-3v)/(v⁵-4v³+3v)=v/(v²-1) (factoring). Then ζ²=v²/(v²-1)²=(vζ-1). So v²/(v²-1)² = v·v/(v²-1) - 1 = v²/(v²-1)-1 = (v²-v²+1)/(v²-1) = 1/(v²-1). So v²/(v²-1)² = 1/(v²-1), giving v²/(v²-1) = 1, so v²=v²-1, 0=-1, 1=0. Contradiction.
   If v⁵-4v³+3v=0: Then v(v⁴-4v²+3)=0. Since m₆₀(0)=1≠0, v≠0. So v⁴-4v²+3=0, giving (v²-1)(v²-3)=0. Check: if v²=1 then m₆₀(v)=1-7+14-8+1=1≠0. If v²=3 then m₆₀(v)=6561-7·729+14·81-8·9+1=6561-5103+1134-72+1=2521. Is this 0? 2521 mod char... if char≠3,5 then 2521 is computed differently. Actually m₆₀(v) with v²=3: v⁸=81, v⁶=27, v⁴=9, v²=3. m₆₀ = 81-7·27+14·9-8·3+1 = 81-189+126-24+1=-5. So m₆₀(v)=-5=0 iff char=5, contradicting hchar5.

Rule out orderOf = 20: ζ²⁰=1. Then ζ³⁰=ζ²⁰·ζ¹⁰=ζ¹⁰=-1.
   Use grind to show contradiction from ζ¹⁰=-1, ζ²-vζ+1=0, m₆₀(v)=0 and char≠5.

The proof involves heavy polynomial arithmetic. Try `grind` for each case.
-/
set_option maxHeartbeats 3200000 in
lemma isPrimitiveRoot_of_quad_m60_root {R : Type*} [Field R]
    (hchar2 : ringChar R ≠ 2) (hchar3 : ringChar R ≠ 3) (hchar5 : ringChar R ≠ 5)
    {v ζ : R} (hquad : ζ ^ 2 - v * ζ + 1 = 0)
    (hm60 : v ^ 8 - 7 * v ^ 6 + 14 * v ^ 4 - 8 * v ^ 2 + 1 = 0) :
    IsPrimitiveRoot ζ 60 := by
  by_cases h1 : ζ = 0 <;> simp_all +decide [ IsPrimitiveRoot.iff_def ];
  have h_order : orderOf ζ = 60 := by
    have h_order : orderOf ζ ∣ 60 ∧ ¬(orderOf ζ ∣ 30) := by
      have h_order : ζ ^ 60 = 1 ∧ ζ ^ 30 ≠ 1 := by
        have h_order : ζ ^ 30 = -1 := by
          grobner
        generalize_proofs at *; simp_all +decide [ pow_succ ] ; (
        rw [ neg_eq_iff_add_eq_zero ] ; intro h; have := ringChar.spec R; simp_all +decide [ ← two_mul ] ;
        specialize this 2 ; simp_all +decide [ Nat.dvd_prime ] ;
        exact absurd ( this.elim 0 1 ) ( by simp +decide ));
      simp_all +decide [ orderOf_dvd_iff_pow_eq_one ];
    have := Nat.le_of_dvd ( by decide ) h_order.1; interval_cases _ : orderOf ζ <;> simp +decide at h_order ⊢;
    · have := pow_orderOf_eq_one ζ; simp_all +decide [ pow_succ ] ;
      grind +splitIndPred;
    · have h_contra : ζ ^ 6 = -1 := by
        have h_contra : ζ ^ 12 = 1 := by
          rw [ ← ‹orderOf ζ = 12›, pow_orderOf_eq_one ];
        have h_contra : ζ ^ 6 = 1 ∨ ζ ^ 6 = -1 := by
          exact eq_or_eq_neg_of_sq_eq_sq _ _ <| by linear_combination' h_contra;
        grind +revert;
      have h_contra : (v ^ 5 - 4 * v ^ 3 + 3 * v) * ζ = v ^ 4 - 3 * v ^ 2 := by
        grind +ring;
      by_cases h : v ^ 5 - 4 * v ^ 3 + 3 * v = 0 <;> simp_all +decide [ sub_eq_iff_eq_add ];
      · rw [ eq_comm ] at h_contra ; simp_all +decide [ sub_eq_iff_eq_add ];
        by_cases hv : v = 0 <;> simp_all +decide [ pow_succ, mul_assoc ];
        by_cases hv : v ^ 2 = 1 <;> simp_all +decide [ sub_eq_iff_eq_add ];
        · grind +ring;
        · have h_contra : v ^ 2 = 3 := by
            exact mul_left_cancel₀ ( pow_ne_zero 2 ‹v ≠ 0› ) ( by linear_combination' h_contra );
          simp_all +decide [ pow_succ, mul_assoc ];
          ring_nf at * ; simp_all +decide [ sub_eq_iff_eq_add ];
          norm_num at hm60;
          have := ringChar.spec R 5; simp_all +decide ;
          have := Nat.le_of_dvd ( by decide ) this; interval_cases _ : ringChar R <;> simp_all +decide ;
          exact absurd ( ‹Subsingleton R›.elim 0 1 ) ( by simp +decide );
      · grind +extAll;
    · have h_contra : ζ ^ 10 = -1 := by
        have := pow_orderOf_eq_one ζ; simp_all +decide [ pow_succ ] ;
        have h_contra : ζ ^ 20 = 1 := by
          linear_combination' this
        have h_contra : ζ ^ 10 = -1 := by
          have h_contra : ζ ^ 10 ≠ 1 := by
            exact fun h => by have := orderOf_dvd_iff_pow_eq_one.mpr h; simp_all +decide ;
          have h_contra : ζ ^ 10 = -1 := by
            exact mul_left_cancel₀ ( sub_ne_zero_of_ne h_contra ) ( by linear_combination' ‹ζ ^ 20 = 1› )
          exact h_contra.symm ▸ by ring;
        exact h_contra.symm ▸ by ring;
      have h_contra : v ^ 5 - 5 * v ^ 3 + 5 * v = 0 := by
        grind +ring;
      have h_contra : v ^ 4 - 5 * v ^ 2 + 5 = 0 := by
        grind;
      have h_contra : v ^ 8 - 7 * v ^ 6 + 14 * v ^ 4 - 8 * v ^ 2 + 1 = 0 := by
        exact hm60;
      rw [ show v ^ 8 = ( v ^ 4 ) ^ 2 by ring, show v ^ 6 = ( v ^ 4 ) * v ^ 2 by ring, show v ^ 4 = 5 * v ^ 2 - 5 by linear_combination' ‹v ^ 4 - 5 * v ^ 2 + 5 = 0› ] at h_contra ; ring_nf at h_contra ; simp_all +decide [ sub_eq_iff_eq_add ] ;
      rw [ show v ^ 4 = 5 * v ^ 2 - 5 by linear_combination' ‹v ^ 4 - 5 * v ^ 2 + 5 = 0› ] at h_contra ; ring_nf at h_contra ; simp_all +decide [ sub_eq_iff_eq_add ] ;
      have h_contra : v ^ 2 = 2 := by
        have h_contra : (3 : R) ≠ 0 := by
          intro h; have := ringChar.spec R; simp_all +decide ;
          specialize this 3 ; simp_all +decide [ Nat.dvd_prime ] ;
          exact absurd ( this.elim 0 1 ) ( by simp +decide );
        exact mul_left_cancel₀ h_contra <| by linear_combination' ‹6 = v ^ 2 * 3›.symm;
      simp_all +decide [ pow_succ ];
      simp_all +decide [ mul_assoc ];
      norm_num at *;
  exact ⟨ by rw [ ← h_order, pow_orderOf_eq_one ], fun l hl => h_order ▸ orderOf_dvd_of_pow_eq_one hl ⟩

/-- Factorization identity: w¹⁰-w⁵+1 = Φ₃₀(w)·Φ₆(w) -/
lemma factor_w10_sub_w5_add_1 {R : Type*} [CommRing R] (w : R) :
    w ^ 10 - w ^ 5 + 1 =
    (w ^ 8 + w ^ 7 - w ^ 5 - w ^ 4 - w ^ 3 + w + 1) * (w ^ 2 - w + 1) := by ring

/-- Chebyshev identity for m₆₀: ζ⁸·m₆₀(ζ+ζ⁻¹) = Φ₃₀(ζ²) = ζ¹⁶+ζ¹⁴-ζ¹⁰-ζ⁸-ζ⁶+ζ²+1. -/
lemma chebyshev_m60_identity {R : Type*} [Field R] (ζ : R) (hζ : ζ ≠ 0) :
    ζ ^ 8 * ((ζ + ζ⁻¹) ^ 8 - 7 * (ζ + ζ⁻¹) ^ 6 + 14 * (ζ + ζ⁻¹) ^ 4 -
    8 * (ζ + ζ⁻¹) ^ 2 + 1) =
    ζ ^ 16 + ζ ^ 14 - ζ ^ 10 - ζ ^ 8 - ζ ^ 6 + ζ ^ 2 + 1 := by
  field_simp; ring

/-
PROBLEM
A primitive 60th root gives a root of m₆₀ via Chebyshev.
    Proof: ζ¹⁰ has order 6, so ζ²⁰-ζ¹⁰+1=0. By the factorization
    ζ²⁰-ζ¹⁰+1 = Φ₃₀(ζ²)·(ζ⁴-ζ²+1), and ζ⁴-ζ²+1≠0 (since ζ² has order 30≠6),
    we get Φ₃₀(ζ²)=0. By the Chebyshev identity, ζ⁸·m₆₀(ζ+ζ⁻¹)=Φ₃₀(ζ²)=0.

PROVIDED SOLUTION
Proof using the factorization approach:

1. ζ ≠ 0: from hζ (primitive root has positive order).
2. ζ^10 has order 60/gcd(10,60) = 60/10 = 6. So IsPrimitiveRoot (ζ^10) 6.
   Use hζ.pow with appropriate divisibility arguments.
3. ζ^10 satisfies Φ₆(ζ^10) = 0, i.e., (ζ^10)² - ζ^10 + 1 = 0, i.e., ζ^20 - ζ^10 + 1 = 0.
   Use isRoot_cyclotomic and cyclotomic_six.
4. By factor_w10_sub_w5_add_1 with w = ζ²:
   (ζ²)^10 - (ζ²)^5 + 1 = (ζ^16+ζ^14-ζ^10-ζ^8-ζ^6+ζ²+1) · (ζ^4-ζ^2+1)
   which is ζ^20 - ζ^10 + 1 = Φ₃₀(ζ²) · Φ₆(ζ²).
   From step 3: LHS = 0, so Φ₃₀(ζ²) · (ζ^4-ζ^2+1) = 0.
5. ζ^4-ζ^2+1 ≠ 0: If ζ^4-ζ^2+1 = 0, then (ζ²)²-ζ²+1 = 0, so Φ₆(ζ²)=0, meaning ζ² is a root of the 6th cyclotomic polynomial. By isRoot_cyclotomic_iff (or directly: (ζ²)^6 = 1, and from the minimal polynomial, orderOf(ζ²) | 6). But orderOf(ζ²) = 30 (since orderOf ζ = 60 and gcd(2,60)=2, so orderOf(ζ²) = 60/2 = 30). 30 doesn't divide 6, contradiction.

   More explicitly: from ζ^4-ζ^2+1=0 → (ζ^2)^3 = ... actually Φ₆(x)=x²-x+1, and x³+1 = (x+1)(x²-x+1), so Φ₆(ζ²)=0 → (ζ²)³=-1 → ζ^6=-1 → ζ^12=1. But orderOf ζ = 60, so ζ^12 ≠ 1 (since 12 < 60 and 60 doesn't divide 12). Contradiction.

6. From step 4 and 5: Φ₃₀(ζ²) = 0, i.e., ζ^16+ζ^14-ζ^10-ζ^8-ζ^6+ζ^2+1 = 0.
7. By chebyshev_m60_identity: ζ^8 · m₆₀(ζ+ζ⁻¹) = ζ^16+ζ^14-ζ^10-ζ^8-ζ^6+ζ^2+1 = 0.
8. ζ^8 ≠ 0 (since ζ ≠ 0). So m₆₀(ζ+ζ⁻¹) = 0.
-/
lemma isPrimitiveRoot_60_implies_m60_root {ζ : K} (hζ : IsPrimitiveRoot ζ 60)
    (hchar2 : ringChar K ≠ 2) :
    (ζ + ζ⁻¹) ^ 8 - 7 * (ζ + ζ⁻¹) ^ 6 + 14 * (ζ + ζ⁻¹) ^ 4 -
    8 * (ζ + ζ⁻¹) ^ 2 + 1 = 0 := by
  have h_factor : ζ ^ 16 + ζ ^ 14 - ζ ^ 10 - ζ ^ 8 - ζ ^ 6 + ζ ^ 2 + 1 = 0 := by
    have h_factor : (ζ ^ 20 - ζ ^ 10 + 1 : K) = 0 := by
      have hζ10 : ζ ^ 60 = 1 := by
        exact hζ.pow_eq_one
      have hζ10_poly : (ζ ^ 10) ^ 2 - ζ ^ 10 + 1 = 0 := by
        have hζ10_poly : (ζ ^ 10) ^ 3 + 1 = 0 := by
          have hζ10_poly : (ζ ^ 10) ^ 3 ≠ 1 := by
            have := hζ.pow_eq_one_iff_dvd 30; simp_all +decide [ pow_succ, mul_assoc ] ;
          generalize_proofs at *; (
          exact mul_left_cancel₀ ( sub_ne_zero_of_ne hζ10_poly ) ( by linear_combination' hζ10 ));
        have hζ10_poly : ζ ^ 10 ≠ -1 := by
          intro h; have := hζ.pow_eq_one; simp_all +decide ;
          have := hζ.2 20; simp_all +decide [ pow_succ, mul_assoc ] ;
        have hζ10_poly : (ζ ^ 10) ^ 2 - ζ ^ 10 + 1 = 0 := by
          exact mul_left_cancel₀ ( sub_ne_zero_of_ne hζ10_poly ) ( by linear_combination' ‹ ( ζ ^ 10 ) ^ 3 + 1 = 0 › )
        exact hζ10_poly
      have hζ20_poly : ζ ^ 20 - ζ ^ 10 + 1 = 0 := by
        linear_combination' hζ10_poly
      exact hζ20_poly;
    have h_factor : (ζ ^ 4 - ζ ^ 2 + 1 : K) ≠ 0 := by
      intro h
      have h_order : ζ ^ 12 = 1 := by
        grind +ring;
      have := hζ.2 12 h_order; simp_all +decide ;
    exact mul_left_cancel₀ h_factor <| by linear_combination' ‹ζ ^ 20 - ζ ^ 10 + 1 = 0›;
  grind +qlia

/-
PROBLEM
Backward: if q ≡ 1 mod 60, then m₆₀ has a root in K.

PROVIDED SOLUTION
Same pattern as m36_root_of_mod36 and m16_root_of_mod16:
1. hmod gives 60 | (q-1).
2. 60 ∣ |Kˣ| = q-1.
3. Kˣ is cyclic, so there exists g with orderOf g = 60.
4. g is a primitive 60th root: IsPrimitiveRoot (g : K) 60.
5. By isPrimitiveRoot_60_implies_m60_root, v = (g:K) + (g:K)⁻¹ satisfies m₆₀(v)=0.

Use IsCyclic.card_orderOf_eq_totient, Finset.card_pos, IsPrimitiveRoot.coe_units_iff.
-/
lemma m60_root_of_mod60 (hmod : Fintype.card K % 60 = 1) :
    ∃ v : K, v ^ 8 - 7 * v ^ 6 + 14 * v ^ 4 - 8 * v ^ 2 + 1 = 0 := by
  obtain ⟨g, hg⟩ : ∃ g : Kˣ, orderOf g = 60 := by
    have h_order : 60 ∣ Fintype.card Kˣ := by
      rw [ Fintype.card_units ] ; omega;
    have h_cyclic : IsCyclic Kˣ := by
      infer_instance;
    obtain ⟨ g, hg ⟩ := h_cyclic.exists_generator;
    obtain ⟨ k, hk ⟩ := h_order;
    use g^k;
    rw [ orderOf_pow' ] <;> norm_num [ hk, orderOf_eq_card_of_forall_mem_zpowers hg ];
    · rw [ Nat.mul_div_cancel _ ( Nat.pos_of_ne_zero ( by rintro rfl; simp_all +decide [ Fintype.card_eq_zero_iff ] ) ) ];
    · nlinarith [ show Fintype.card Kˣ > 0 from Fintype.card_pos ];
  -- By isPrimitiveRoot_60_implies_m60_root, v = (g:K) + (g:K)⁻¹ satisfies m₆₀(v)=0.
  have hv : (g.val + g.val⁻¹) ^ 8 - 7 * (g.val + g.val⁻¹) ^ 6 + 14 * (g.val + g.val⁻¹) ^ 4 - 8 * (g.val + g.val⁻¹) ^ 2 + 1 = 0 := by
    have h_primitive_root : IsPrimitiveRoot (g : K) 60 := by
      rw [ IsPrimitiveRoot.iff_def ];
      simp +decide [ ← hg, ← Units.val_pow_eq_pow_val, orderOf_dvd_iff_pow_eq_one ];
    convert isPrimitiveRoot_60_implies_m60_root h_primitive_root _ using 1;
    intro h; have := FiniteField.card K ( ringChar K ) ; simp_all +decide ;
    rcases this with ⟨ n, hn ⟩ ; have := congr_arg ( · % 2 ) hmod ; norm_num [ Nat.pow_mod, hn ] at this;
  exact ⟨ _, hv ⟩

/-
PROBLEM
Forward: if m₆₀ has a root in K (with q ≡ 1 mod 4, char ≠ 2,3,5),
then q ≡ 1 mod 60.

PROVIDED SOLUTION
Identical pattern to mod36_of_m36_root in ThetaCycles.lean but with 60 instead of 36.

Case split on whether X²-vX+1 has a root in K.

Case 1: obtain ⟨ζ, hquad⟩ from the root. Then by isPrimitiveRoot_of_quad_m60_root (hchar2 hchar3 hchar5 hquad hm60), IsPrimitiveRoot ζ 60. Then orderOf ζ = 60. Since ζ ∈ K*, ζ is a unit with orderOf 60, so 60 | |K*| = q-1, hence q ≡ 1 mod 60.

Case 2: X²-vX+1 has no roots in K (irreducible). Build AdjoinRoot. Frobenius gives ζ^q=ζ⁻¹ (since ζ∉K), so ζ^(q+1)=1. From IsPrimitiveRoot ζ 60 in L: 60 | q+1, q ≡ 59 mod 60. But q ≡ 1 mod 4 (mod4_of_neg_one_is_square), contradiction since 59 mod 4 = 3.

For Case 2, need to transfer char hypotheses to L and compute in AdjoinRoot.
-/
set_option maxHeartbeats 1600000 in
lemma mod60_of_m60_root (hchar2 : ringChar K ≠ 2) (hchar3 : ringChar K ≠ 3) (hchar5 : ringChar K ≠ 5)
    (hsplit : ∃ i : K, i ^ 2 = -1)
    (hroot : ∃ v : K, v ^ 8 - 7 * v ^ 6 + 14 * v ^ 4 - 8 * v ^ 2 + 1 = 0) :
    Fintype.card K % 60 = 1 := by
  obtain ⟨ v, hv ⟩ := hroot;
  -- Let $w$ be a root of $w^2 - vw + 1 = 0$ in some extension field of $K$.
  obtain ⟨w, hw⟩ : ∃ w : AlgebraicClosure K, w ^ 2 - (algebraMap K (AlgebraicClosure K)) v * w + 1 = 0 := by
    obtain ⟨w, hw⟩ : ∃ w : AlgebraicClosure K, w ^ 2 - (algebraMap K (AlgebraicClosure K)) v * w + 1 = 0 := by
      have h_alg_closed : IsAlgClosed (AlgebraicClosure K) := by
        infer_instance
      have := h_alg_closed.exists_root ( Polynomial.X ^ 2 - Polynomial.C ( algebraMap K ( AlgebraicClosure K ) v ) * Polynomial.X + 1 ) ?_ <;> norm_num at *;
      · exact this;
      · rw [ Polynomial.degree_add_eq_left_of_degree_lt ] <;> rw [ Polynomial.degree_sub_eq_left_of_degree_lt ] <;> by_cases hv : v = 0 <;> simp +decide [ hv ];
    use w;
  -- By Lemma 25, $w$ is a primitive 60th root of unity.
  have hw_primitive : IsPrimitiveRoot w 60 := by
    apply isPrimitiveRoot_of_quad_m60_root (by
    have h_char_eq : ringChar (AlgebraicClosure K) = ringChar K := by
      grind +suggestions;
    aesop) (by
    grind +suggestions) (by
    grind +suggestions) hw (by
    simpa using congr_arg ( algebraMap K ( AlgebraicClosure K ) ) hv);
  -- Since $w$ is a primitive 60th root of unity, its order is 60.
  have hw_order : orderOf w = 60 := by
    rw [ hw_primitive.eq_orderOf ];
  -- Since $w$ is a root of $w^2 - vw + 1 = 0$, we have $w^q = w$ or $w^q = w^{-1}$.
  have hw_q : w ^ (Fintype.card K) = w ∨ w ^ (Fintype.card K) = w⁻¹ := by
    have hw_q : w ^ (Fintype.card K) = w ∨ w ^ (Fintype.card K) = w⁻¹ := by
      have h_poly : w ^ 2 - (algebraMap K (AlgebraicClosure K)) v * w + 1 = 0 := hw
      have h_poly_q : (w ^ (Fintype.card K)) ^ 2 - (algebraMap K (AlgebraicClosure K)) v * w ^ (Fintype.card K) + 1 = 0 := by
        convert congr_arg ( fun x => x ^ Fintype.card K ) h_poly using 1 <;> ring;
        · have h_frobenius : ∀ (a b : AlgebraicClosure K), (a + b) ^ Fintype.card K = a ^ Fintype.card K + b ^ Fintype.card K := by
            have h_frobenius : ∀ (a b : AlgebraicClosure K), (a + b) ^ (ringChar K) = a ^ (ringChar K) + b ^ (ringChar K) := by
              haveI := Fact.mk ( show Nat.Prime ( ringChar K ) from by
                                  have := FiniteField.card K ( ringChar K ) ; aesop; ) ; simp +decide [ add_pow_char ] ;
            have h_frobenius : ∀ (n : ℕ) (a b : AlgebraicClosure K), (a + b) ^ (ringChar K ^ n) = a ^ (ringChar K ^ n) + b ^ (ringChar K ^ n) := by
              intro n; induction n <;> simp_all +decide [ pow_succ, pow_mul ] ;
            have := FiniteField.card K ( ringChar K ) ; aesop;
          simp +decide [ h_frobenius, pow_mul ];
          have h_frobenius : ∀ (a b : AlgebraicClosure K), (a - b) ^ Fintype.card K = a ^ Fintype.card K - b ^ Fintype.card K := by
            intro a b; specialize h_frobenius ( a - b ) b; aesop;
          simp +decide [ h_frobenius, pow_right_comm ] ; ring;
          exact congr_arg _ ( by rw [ ← map_pow, FiniteField.pow_card ] );
        · rw [ zero_pow ( Fintype.card_ne_zero ) ]
      grind +ring;
    exact hw_q;
  cases' hw_q with hw_q hw_q;
  · have hw_q : w ^ (Fintype.card K - 1) = 1 := by
      cases n : Fintype.card K <;> simp_all +decide [ pow_succ' ];
      by_cases hw : w = 0 <;> aesop;
    have := orderOf_dvd_iff_pow_eq_one.mpr hw_q; simp_all +decide ;
    obtain ⟨ k, hk ⟩ := this; rw [ tsub_eq_iff_eq_add_of_le ( Nat.succ_le_of_lt ( Fintype.card_pos ) ) ] at hk; norm_num [ hk, Nat.add_mod ] ;
  · -- Since $w^q = w^{-1}$, we have $w^{q+1} = 1$.
    have hw_q_plus_one : w ^ (Fintype.card K + 1) = 1 := by
      grind;
    have := orderOf_dvd_iff_pow_eq_one.mpr hw_q_plus_one; simp_all +decide ;
    obtain ⟨ k, hk ⟩ := this; replace hk := congr_arg ( · % 4 ) hk; norm_num [ Nat.add_mod, Nat.mul_mod ] at hk;
    have := mod4_of_neg_one_is_square hchar2 hsplit; simp_all +decide ;

/-- m₆₀ existence criterion: m₆₀ has a root in K ↔ q ≡ 1 mod 60
    (given q ≡ 1 mod 4, char ≠ 2). -/
theorem m60_root_iff_mod60 (hchar2 : ringChar K ≠ 2) (hchar3 : ringChar K ≠ 3) (hchar5 : ringChar K ≠ 5)
    (hsplit : ∃ i : K, i ^ 2 = -1) :
    (∃ v : K, v ^ 8 - 7 * v ^ 6 + 14 * v ^ 4 - 8 * v ^ 2 + 1 = 0) ↔
    Fintype.card K % 60 = 1 :=
  ⟨mod60_of_m60_root hchar2 hchar3 hchar5 hsplit, m60_root_of_mod60⟩

/-! ## Part 3: Connecting octic roots to m₆₀ roots -/

/-
PROBLEM
The octic factor has a root iff m₆₀* has a root, iff m₆₀ has a root.
    Uses the bridge lemma and invertible substitution.

PROVIDED SOLUTION
The octic x⁸+7x⁶+14x⁴+8x²+1 has a nonzero root iff m₆₀ has a root.

The chain: octic root x≠0 ↔ m₆₀*(i/x)=0 (bridge) ↔ m₆₀ root (reciprocal).

Forward: If x⁸+7x⁶+14x⁴+8x²+1=0 and x≠0, then by four_cycle_octic_iff_m60,
(i/x)⁸-8(i/x)⁶+14(i/x)⁴-7(i/x)²+1=0. This is m₆₀*(i/x)=0. By m60star_root_iff_m60_root, m₆₀ has a root.

Backward: If m₆₀ has a root v, then by m60star_root_iff_m60_root.mpr, m₆₀* has a root u. Then u≠0 (m₆₀*(0)=1≠0). Set x=i/u, then x≠0 and by the bridge lemma, x⁸+7x⁶+14x⁴+8x²+1=0.

Use four_cycle_octic_iff_m60 and m60star_root_iff_m60_root.
-/
lemma octic_root_iff_m60_root (hchar2 : ringChar K ≠ 2)
    (hsplit : ∃ i : K, i ^ 2 = -1) :
    (∃ x : K, x ≠ 0 ∧ x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1 = 0) ↔
    (∃ v : K, v ^ 8 - 7 * v ^ 6 + 14 * v ^ 4 - 8 * v ^ 2 + 1 = 0) := by
  have h_bridge : ∀ x : K, x ≠ 0 → (x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1 = 0 ↔ (hsplit.choose / x) ^ 8 - 8 * (hsplit.choose / x) ^ 6 + 14 * (hsplit.choose / x) ^ 4 - 7 * (hsplit.choose / x) ^ 2 + 1 = 0) := by
    intro x hx_nonzero
    apply four_cycle_octic_iff_m60 hx_nonzero hsplit.choose_spec;
  constructor;
  · rintro ⟨ x, hx, hx' ⟩;
    exact m60star_root_iff_m60_root.mp ⟨ _, h_bridge x hx |>.1 hx' ⟩;
  · rintro ⟨ v, hv ⟩;
    use hsplit.choose / v⁻¹;
    grind

/-
PROBLEM
The quartic factor has a root iff m₁₆ has a root.
    Uses the bridge lemma and invertible substitution.

PROVIDED SOLUTION
The quartic 2x⁴+4x²+1 has a root x≠0 iff m₁₆ has a root, via the substitution u=i/x where i²=-1.

Forward: If 2x⁴+4x²+1=0 and x≠0, then by four_cycle_quartic_iff_m16, (i/x)⁴-4(i/x)²+2=0. Set u=i/x.

Backward: If u⁴-4u²+2=0, then u≠0 (since m₁₆(0)=2≠0). Set x=i/u. Then x≠0 and by the bridge lemma (used in reverse), 2x⁴+4x²+1=0.

The key is four_cycle_quartic_iff_m16 from ThetaCycles.lean: for x≠0, i²=-1:
2*x^4+4*x^2+1 = 0 ↔ (i/x)^4-4*(i/x)^2+2 = 0

Proof:
constructor
· rintro ⟨x, hx, hq⟩; obtain ⟨i, hi⟩ := hsplit
  exact ⟨i/x, (four_cycle_quartic_iff_m16 hx hi).mp hq⟩
· rintro ⟨u, hu⟩; obtain ⟨i, hi⟩ := hsplit
  have hu_ne : u ≠ 0 := by intro h; simp [h] at hu; norm_num at hu
  have hi_ne : i ≠ 0 := by intro h; simp [h] at hi
  refine ⟨i/u, div_ne_zero hi_ne hu_ne, ?_⟩
  have hix : i/(i/u) = u := by field_simp
  exact (four_cycle_quartic_iff_m16 (div_ne_zero hi_ne hu_ne) hi).mpr (by rw [hix]; exact hu)
-/
lemma quartic_root_iff_m16_root (hchar2 : ringChar K ≠ 2)
    (hsplit : ∃ i : K, i ^ 2 = -1) :
    (∃ x : K, x ≠ 0 ∧ 2 * x ^ 4 + 4 * x ^ 2 + 1 = 0) ↔
    (∃ u : K, u ^ 4 - 4 * u ^ 2 + 2 = 0) := by
  constructor <;> intro h;
  · obtain ⟨x, hx_ne_zero, hx_eq⟩ := h
    obtain ⟨i, hi⟩ := hsplit
    use i / x;
    grobner;
  · obtain ⟨ u, hu ⟩ := h
    obtain ⟨ i, hi ⟩ := hsplit
    use i / u
    have hu_ne : u ≠ 0 := by
      intro h; simp_all +decide ;
      exact absurd hu ( by have := two_ne_zero_of_ringChar_ne_two hchar2; aesop )
    have hi_ne : i ≠ 0 := by
      grind
    have hix : i/(i/u) = u := by
      rw [ div_div_cancel₀ hi_ne ]
    exact ⟨by
    exact div_ne_zero hi_ne hu_ne, by
      grind⟩

/-! ## Part 4: Root counting (separability and coprimality) -/

/-- The quartic 2x⁴+4x²+1 has no root at 0. -/
lemma quartic_ne_zero_at_zero : (2 : K) * (0 : K) ^ 4 + 4 * (0 : K) ^ 2 + 1 ≠ 0 := by
  simp

/-- The octic has no root at 0. -/
lemma octic_ne_zero_at_zero :
    (0 : K) ^ 8 + 7 * (0 : K) ^ 6 + 14 * (0 : K) ^ 4 + 8 * (0 : K) ^ 2 + 1 ≠ 0 := by
  simp

/-
PROBLEM
The quartic roots are distinct from period-2 roots (2x²+1=0 roots).
    If 2x⁴+4x²+1=0 then 2x²+1≠0.

PROVIDED SOLUTION
If 2x⁴+4x²+1=0 and 2x²+1=0, then from the second equation x²=-1/2, so x⁴=1/4. Then 2·(1/4)+4·(-1/2)+1 = 1/2-2+1 = -1/2 ≠ 0 (in char≠2). Contradiction.

More concretely: if 2x²+1=0, then 2x⁴+4x²+1 = 2x²·x²+4x²+1 = (-1)·x²+4x²+1 = 3x²+1 (using 2x²=-1).
Actually from 2x²+1=0: 2x²=-1. Then 2x⁴ = x²·2x² = x²·(-1) = -x². So 2x⁴+4x²+1 = -x²+4x²+1 = 3x²+1.
From 2x²=-1: x²=-1/2. So 3x²+1 = -3/2+1 = -1/2. In char≠2, -1/2≠0.

Alternatively: linear_combination approach. From h1: 2x⁴+4x²+1=0 and h2: 2x²+1=0:
h1 - x²·h2 = 2x⁴+4x²+1-2x⁴-x² = 3x²+1 = 0.
Also h2 gives 2x²=-1, so x²=-1/2, so 3(-1/2)+1 = -1/2 = 0. So 1/2=0, i.e., 2=0, contradicting char≠2.

Proof: intro h2. have := linear_combination h1 - x²·h2 (giving 3x²+1=0). Then from h2: x² = -(1/2). Substituting: 3·(-1/2)+1 = -1/2 = 0, so 1=0 or 2=0, contradiction.
-/
lemma quartic_root_not_period2 {x : K} (hchar2 : ringChar K ≠ 2)
    (hq : 2 * x ^ 4 + 4 * x ^ 2 + 1 = 0) : 2 * x ^ 2 + 1 ≠ 0 := by
  grind +qlia

/-
PROBLEM
The octic roots that aren't period-2 roots: if x⁸+7x⁶+14x⁴+8x²+1=0 and
    2x²+1≠0, then theta2 x ≠ x.

PROVIDED SOLUTION
If x⁸+7x⁶+14x⁴+8x²+1=0 and 2x²+1≠0 and x≠0, then θ²(x)≠x.

By theta2_eq_x_iff (from ThetaCycles.lean): θ²(x)=x ↔ 2x²+1=0 (when x≠0 and char≠2).
Since 2x²+1≠0 (hypothesis h2), we have θ²(x)≠x.

So the proof is: intro htheta2; exact h2 ((theta2_eq_x_iff hx hchar2).mp htheta2)
-/
lemma octic_root_not_period2_implies {x : K} (hchar2 : ringChar K ≠ 2)
    (hx : x ≠ 0) (hoct : x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1 = 0)
    (h2 : 2 * x ^ 2 + 1 ≠ 0) : theta2 x ≠ x := by
  -- Apply the lemma theta2_eq_x_iff to conclude that theta2 x ≠ x.
  apply (theta2_eq_x_iff hx hchar2).not.mpr h2

/-
PROBLEM
Number of roots of quartic 2X⁴+4X²+1 equals 0 or 4.
    When it equals 4, the polynomial splits with distinct roots (separable).

PROVIDED SOLUTION
The quartic 2X⁴+4X²+1 has either 0 or 4 roots.

If it has no roots: filter card = 0. The if-then-else evaluates to 0. ✓

If it has a root x₀: it has exactly 4 roots (separability).

The polynomial f(X) = 2X⁴+4X²+1 has derivative f'(X) = 8X³+8X = 8X(X²+1).
f and f' share a root only if x₀ = 0 (but f(0) = 1 ≠ 0) or x₀²+1=0 (but then f(x₀)=2·1+4·(-1)+1=-1≠0, wait: 2x₀⁴+4x₀²+1 = 2·(x₀²)²+4x₀²+1. If x₀²=-1: 2·1-4+1=-1. So f(x₀)=-1≠0 if char≠1.).

Actually the cleaner approach: f is a polynomial in y=x². As a polynomial g(y)=2y²+4y+1 of degree 2, it has at most 2 roots in y. For each y-root, x²=y gives 0 or 2 values of x. So f has at most 4 roots.

When f has roots: g(y)=2y²+4y+1 is a degree 2 polynomial. Its discriminant is 16-8=8. In char≠2, g is separable (disc≠0 when 8≠0, i.e., char∤8, i.e., char≠2). So g has exactly 2 distinct roots y₁, y₂. For each yₖ, x²=yₖ has either 0 or 2 solutions (since char≠2, every element is either a square or not, and if it's a square, it has exactly 2 square roots).

If g has roots, does each root give square values? If f has a root x₀, then y₀=x₀² is a root of g. So y₀ is a square (= x₀²). Also the other root y₁ = (-4-2y₀)/(2·2) = -2-y₀ (Vieta). Is y₁ a square?

Actually, the cleanest approach is: show Polynomial.card_roots ≤ natDegree. And when the polynomial splits, card_roots = natDegree (separability). And then show the filter card equals card_roots.

For the proof: use Polynomial.card_roots_le_degree to show ≤ 4. For the exact count, use separability: f = 2X⁴+4X²+1 is separable iff gcd(f, f') = 1. f' = 8X³+8X = 8X(X²+1). Since f(0)=1≠0 and f at roots of X²+1=-1 gives 2-4+1=-1≠0, gcd(f,f')=1 in char≠2.

So f is separable of degree 4. If it has any root, it splits into distinct linear factors over the splitting field. Since K is a finite field, f splits over K iff all roots are in K. If one root exists, we need all 4 roots to be in K.

Hmm, this isn't immediately obvious. Let me think...

Actually, f(X) = 2X⁴+4X²+1 is a polynomial in X² only (even function). If x is a root, so is -x. And g(y) = 2y²+4y+1 where y=x². If y₀ is a root of g and y₀ has a square root in K, then ±√y₀ are roots of f. The other root of g is y₁ = -2-y₀ (Vieta). Does y₁ have a square root?

y₀·y₁ = 1/2 (Vieta, constant term/leading coefficient). So y₁ = 1/(2y₀). If y₀ = x₀², then y₁ = 1/(2x₀²). Is y₁ a square? y₁ = (1/(x₀√2))² if √2 exists. Hmm, not necessarily.

Actually: f has a root ↔ m₁₆ has a root (by quartic_root_iff_m16_root) ↔ q ≡ 1 mod 16 (by m16_root_iff_mod16). And 16 | q-1 means the multiplicative group has an element of order 16. In that case, f splits completely over K (all 4 roots are in K).

Why does m₁₆ having a root imply f splits? Because m₁₆ is related to the 16th cyclotomic polynomial, and when 16 | q-1, the cyclotomic polynomial splits. Then the substitution gives all roots of f.

This is getting circular. Let me try a direct approach: show that the filter has card 0 or 4 using Polynomial.card_roots and the structure of the polynomial.

Use: multiset.card (f.roots) ≤ 4, and the filter set is exactly the roots. When f has a root, show it has exactly 4 by computing the discriminant or using separability + the fact that it factors into quadratics in y=x².

Actually, the simplest approach might be to just use the subagent with the hint that this is a degree 4 separable polynomial over a finite field, so it has 0 or 4 roots.
-/
lemma quartic_root_card (hchar2 : ringChar K ≠ 2) :
    (Finset.univ.filter (fun x : K => 2 * x ^ 4 + 4 * x ^ 2 + 1 = 0)).card =
    if (∃ x : K, 2 * x ^ 4 + 4 * x ^ 2 + 1 = 0) then 4 else 0 := by
  -- Let's denote the polynomial by $f(x) = 2x^4 + 4x^2 + 1$.
  set f : Polynomial K := Polynomial.C 2 * Polynomial.X ^ 4 + Polynomial.C 4 * Polynomial.X ^ 2 + Polynomial.C 1;
  split_ifs with h;
  · -- Since $f$ is a polynomial of degree 4, it can have at most 4 roots. Given that we have 4 roots, there can't be any more.
    have h_card : (Finset.filter (fun x => f.eval x = 0) Finset.univ).card ≤ 4 := by
      have h_card : (Finset.filter (fun x => f.eval x = 0) Finset.univ).card ≤ f.roots.toFinset.card := by
        refine' Finset.card_le_card _;
        simp +decide [ Finset.subset_iff ];
        simp +zetaDelta at *;
        exact fun x hx => ⟨ ne_of_apply_ne ( Polynomial.eval 0 ) ( by simp +decide [ hx ] ), hx ⟩;
      refine' le_trans h_card ( le_trans ( Multiset.toFinset_card_le _ ) ( le_trans ( Polynomial.card_roots' _ ) _ ) );
      rw [ Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> by_cases h : ( 2 : K ) = 0 <;> simp +decide [ h ];
      · grind;
      · by_cases h' : ( 4 : K ) = 0 <;> simp +decide [ h', Polynomial.natDegree_C_mul_X_pow ];
    obtain ⟨ x, hx ⟩ := h;
    -- Since $x$ is a root of $f$, we know that $-x$ is also a root. Additionally, the roots of $x^2 = \frac{-2 + \sqrt{2}}{2}$ and $x^2 = \frac{-2 - \sqrt{2}}{2}$ are distinct and non-zero.
    have h_roots : Finset.filter (fun x => f.eval x = 0) Finset.univ ⊇ {x, -x, (x ^ 2 + 1) / x, -(x ^ 2 + 1) / x} := by
      simp +decide [ Finset.insert_subset_iff, hx ];
      norm_num +zetaDelta at *;
      grind;
    have h_distinct : x ≠ -x ∧ x ≠ (x ^ 2 + 1) / x ∧ x ≠ -(x ^ 2 + 1) / x ∧ -x ≠ (x ^ 2 + 1) / x ∧ -x ≠ -(x ^ 2 + 1) / x ∧ (x ^ 2 + 1) / x ≠ -(x ^ 2 + 1) / x := by
      grind +splitIndPred;
    have h_card_eq : (Finset.filter (fun x => f.eval x = 0) Finset.univ).card ≥ 4 := by
      exact le_trans ( by rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton ] <;> aesop ) ( Finset.card_mono h_roots );
    convert le_antisymm h_card h_card_eq using 2 ; aesop;
  · aesop

-- The original statements below are INCORRECT in characteristic 3:
-- In char 3, the octic x⁸+7x⁶+14x⁴+8x²+1 = (2x⁴+4x²+1)² (as polynomials in x²),
-- so quartic roots are also octic roots, breaking the disjointness assumption
-- in four_cycle_filter_card_eq and making the count 4 instead of 0 or 8 in
-- octic_nonperiod2_root_card. The key identity:
--   4·(y⁴+7y³+14y²+8y+1) + 3·(2y+1) = (2y²+4y+1)·(2y²+10y+7)
-- shows that at a quartic root (2y²+4y+1=0), the octic equals -3(2y+1)/4,
-- which is 0 in char 3 but nonzero in char ≠ 2,3.
-- Corrected versions below add `hchar3 : ringChar K ≠ 3`.

/-! ### Coprimality helpers -/

/-- Key identity: 4·octic + 3·(2x²+1) = quartic · (2x⁴+10x²+7) as polynomials in x² -/
lemma octic_quartic_identity (x : K) :
    4 * (x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1) + 3 * (2 * x ^ 2 + 1) =
    (2 * x ^ 4 + 4 * x ^ 2 + 1) * (2 * x ^ 4 + 10 * x ^ 2 + 7) := by
  ring

/-
PROBLEM
Quartic roots and octic roots are disjoint in char ≠ 2, 3.

PROVIDED SOLUTION
From the identity octic_quartic_identity: 4·octic + 3·(2x²+1) = quartic·Q. If quartic=0 and octic=0, then 3·(2x²+1)=0. Since 2x²+1≠0 (by quartic_root_not_period2), and 3≠0 (char≠3, use ringChar to derive (3:K)≠0 from hchar3), we get a contradiction.
-/
lemma octic_ne_zero_of_quartic_zero (hchar2 : ringChar K ≠ 2) (hchar3 : ringChar K ≠ 3)
    {x : K} (hq : 2 * x ^ 4 + 4 * x ^ 2 + 1 = 0) :
    x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1 ≠ 0 := by
  have h_char3 : (3 : K) ≠ 0 := by
    intro h; have := ringChar.spec K; simp_all +decide ;
    specialize this 3 ; simp_all +decide [ Nat.dvd_prime ];
    exact not_subsingleton _ this;
  grind

/-
PROBLEM
In char 5, the octic equals (2x²+1)⁴.

PROVIDED SOLUTION
The difference (x^8+7x^6+14x^4+8x^2+1) - (2x^2+1)^4 = x^8+7x^6+14x^4+8x^2+1 - 16x^8-32x^6-24x^4-8x^2-1 = -15x^8-25x^6-10x^4 = -5x^4(3x^4+5x^2+2). In char 5, -5=0, so the difference is 0. Use that (5:K)=0 from hchar5 being ringChar K = 5, then show the polynomial identity holds by showing (5:K)=0 implies the ring identity. Use have h5 : (5:K) = 0 from CharP.cast_eq_zero_iff and ringChar.charP.
-/
lemma octic_eq_period2_pow4_char5 (hchar5 : ringChar K = 5) (x : K) :
    x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1 =
    (2 * x ^ 2 + 1) ^ 4 := by
  -- Since $5 = 0$ in $K$, we can simplify the coefficients modulo 5.
  have h_mod5 : (5 : K) = 0 := by
    rw [ ← Nat.cast_ofNat, ← hchar5, ringChar.spec ];
  grind +ring

/-
PROBLEM
Octic roots have 2x²+1 ≠ 0 in char ≠ 2, 5.

PROVIDED SOLUTION
The octic evaluated at y = x² = -1/2 (where 2x²+1=0) gives: (-1/2)⁴+7(-1/2)³+14(-1/2)²+8(-1/2)+1 = 1/16-7/8+14/4-4+1 = (1-14+56-64+16)/16 = -5/16. So if 2x²+1=0 and octic=0, then -5/16=0, hence 5=0, hence ringChar K | 5, hence ringChar K = 5 (since 5 is prime), contradicting hchar5. Use linear_combination with hq and hoct.
-/
lemma octic_root_period2_coprime (hchar2 : ringChar K ≠ 2) (hchar5 : ringChar K ≠ 5)
    {x : K} (hoct : x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1 = 0) :
    2 * x ^ 2 + 1 ≠ 0 := by
  contrapose! hchar5;
  have h_char_5 : (5 : K) = 0 := by
    grind;
  have := ringChar.spec K;
  specialize this 5 ; simp_all +decide [ Nat.dvd_prime ];
  exact this.resolve_left ( by exact not_subsingleton _ )

/-
PROBLEM
An octic non-period-2 root implies char ≠ 5.

PROVIDED SOLUTION
Proof by contradiction. Assume ringChar K = 5. Then by octic_eq_period2_pow4_char5, octic = (2x²+1)⁴. So octic(x)=0 means (2x²+1)⁴=0, hence 2x²+1=0 (zero divisors in a field). This contradicts h2.
-/
lemma char_ne_5_of_octic_nonperiod2 {x : K}
    (hoct : x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1 = 0)
    (h2 : 2 * x ^ 2 + 1 ≠ 0) : ringChar K ≠ 5 := by
  contrapose! h2; haveI := Fact.mk ‹_›; simp_all +decide [ pow_succ', mul_assoc, mul_comm, mul_left_comm ] ;
  have h_char : (5 : K) = 0 := by
    rw [ ← Nat.cast_ofNat, ← h2, ringChar.spec ]
  generalize_proofs at *; (
  grind +ring)

/-! ### Orbit construction helpers for octic root counting -/

/-
PROBLEM
θ(−x) = −θ(x) for x ≠ 0.

PROVIDED SOLUTION
Unfold theta. theta(-x) = -x + (-x)⁻¹ = -x + (-(x⁻¹)) = -(x + x⁻¹) = -theta(x). Use that (-x)⁻¹ = -(x⁻¹) in a field, then unfold theta and ring.
-/
lemma theta_neg_eq (x : K) (hx : x ≠ 0) : theta (-x) = -theta x := by
  unfold theta; ring

/-
PROBLEM
θ²(x) = −x iff 2x⁴+4x²+1 = 0 (for x ≠ 0, char ≠ 2).

PROVIDED SOLUTION
Unfold theta2, theta. We have theta2 x = (x⁴+3x²+1)/(x(x²+1)) (by theta2_eq_div). So theta2 x = -x ↔ (x⁴+3x²+1)/(x(x²+1)) = -x ↔ x⁴+3x²+1 = -x²(x²+1) ↔ x⁴+3x²+1 = -x⁴-x² ↔ 2x⁴+4x²+1 = 0. Use theta2_eq_div and field_simp.
-/
lemma theta2_eq_neg_iff {x : K} (hx : x ≠ 0) (hchar2 : ringChar K ≠ 2)
    (h1 : x ^ 2 + 1 ≠ 0) :
    theta2 x = -x ↔ 2 * x ^ 4 + 4 * x ^ 2 + 1 = 0 := by
  rw [theta2];
  rw [theta, theta];
  field_simp;
  grind +ring

/-
PROBLEM
If x is an octic non-period-2 root with char ≠ 2,3, then θ(x) is also
    an octic root with 2θ(x)²+1 ≠ 0.

PROVIDED SOLUTION
Since octic(x)=0 and the product (2x²+1)(2x⁴+4x²+1)(octic(x))=0 holds, and we know x≠0 and 2x²+1≠0, we get theta4 x = x by fourth_iterate_factored.

Since theta4(θ(x)) = θ(theta4(x)) = θ(x) (by definition theta4 = θ⁴, so θ⁵ = θ∘θ⁴ = θ⁴∘θ), θ(x) is also theta4-fixed.

θ(x) ≠ 0: Since x²+1≠0 (hypothesis h1) and x≠0, theta_ne_zero_iff gives θ(x) ≠ 0.

By fourth_iterate_factored on θ(x): (2θ(x)²+1)(2θ(x)⁴+4θ(x)²+1)(octic(θ(x)))=0.

Claim 1: 2θ(x)²+1 ≠ 0.
If 2θ(x)²+1=0, then theta2(θ(x))=θ(x) by theta2_eq_x_iff. But theta2(θ(x)) = θ(theta2(x)) = ... actually theta2(θ(x)) = θ²(θ(x)) = θ³(x). So θ³(x)=θ(x), meaning θ²(x)=x (since θ(θ²(x))=θ³(x)=θ(x)=θ(x), so ... hmm).
Actually: theta2(θ(x)) = theta(theta(θ(x))) = θ³(x). If theta2(θ(x))=θ(x), then θ³(x)=θ(x). Applying theta: θ⁴(x)=θ²(x), i.e., x = theta2(x) (since theta4 x = x). But 2x²+1≠0, so theta2(x)≠x by theta2_eq_x_iff. Contradiction.

Claim 2: 2θ(x)⁴+4θ(x)²+1 ≠ 0.
If 2θ(x)⁴+4θ(x)²+1=0, then by theta2_eq_neg_iff, theta2(θ(x))=-θ(x).
theta2(θ(x)) = θ³(x). So θ³(x) = -θ(x). Apply θ: θ⁴(x)=θ(-θ(x))=-θ²(x) (using theta_neg_eq). But θ⁴(x)=x. So x = -θ²(x), i.e., theta2(x) = -x. By theta2_eq_neg_iff, 2x⁴+4x²+1=0 (x is a quartic root).
But by octic_ne_zero_of_quartic_zero (char≠3), octic(x)≠0. Contradiction with octic(x)=0.

So octic(θ(x))=0. And 2θ(x)²+1≠0 (from Claim 1). And θ(x)≠0.
-/
lemma octic_root_preserved_by_theta (hchar2 : ringChar K ≠ 2) (hchar3 : ringChar K ≠ 3)
    {x : K} (hx : x ≠ 0) (h1 : x ^ 2 + 1 ≠ 0)
    (hoct : x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1 = 0)
    (h2 : 2 * x ^ 2 + 1 ≠ 0) :
    theta x ^ 8 + 7 * theta x ^ 6 + 14 * theta x ^ 4 + 8 * theta x ^ 2 + 1 = 0 ∧
    2 * theta x ^ 2 + 1 ≠ 0 ∧ theta x ≠ 0 := by
  refine' ⟨ _, _, _ ⟩ <;> contrapose! hchar2 <;> simp_all +decide [ theta ];
  · grind;
  · grind;
  · grind

/-- The octic polynomial is even: octic(-x) = octic(x). -/
lemma octic_eval_neg (x : K) :
    (-x) ^ 8 + 7 * (-x) ^ 6 + 14 * (-x) ^ 4 + 8 * (-x) ^ 2 + 1 =
    x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1 := by
  ring

/-- Octic root implies x ≠ 0. -/
lemma octic_root_ne_zero {x : K}
    (hoct : x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1 = 0) : x ≠ 0 := by
  intro h; subst h; simp at hoct

/-
PROBLEM
Octic root implies x² + 1 ≠ 0.

PROVIDED SOLUTION
If x²+1=0, then x²=-1, x⁴=1, x⁸=1. The octic becomes 1+7(-1)+14(1)+8(-1)+1 = 1-7+14-8+1 = 1. So octic = 1 ≠ 0, contradiction.
-/
lemma octic_root_sq_add_one_ne {x : K}
    (hoct : x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1 = 0) : x ^ 2 + 1 ≠ 0 := by
  grind

/-
PROBLEM
Upper bound: the octic non-period-2 filter has ≤ 8 elements.

PROVIDED SOLUTION
The filter is a subset of the roots of the polynomial f = X⁸+7X⁶+14X⁴+8X²+1. This polynomial has degree 8 (leading coefficient 1). By Polynomial.card_roots_le_degree, the number of roots is ≤ 8. The filter has card ≤ the number of roots ≤ 8.

Set f := X^8 + C 7 * X^6 + C 14 * X^4 + C 8 * X^2 + C 1. Show card of filter ≤ f.roots.toFinset.card ≤ f.roots.card ≤ f.natDegree ≤ 8.
-/
lemma octic_nonperiod2_card_le_8 :
    (Finset.univ.filter (fun x : K =>
      x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1 = 0 ∧
      2 * x ^ 2 + 1 ≠ 0)).card ≤ 8 := by
  -- The polynomial $x^8 + 7x^6 + 14x^4 + 8x^2 + 1$ has degree 8, so it can have at most 8 roots.
  have h_deg : (Polynomial.X ^ 8 + Polynomial.C 7 * Polynomial.X ^ 6 + Polynomial.C 14 * Polynomial.X ^ 4 + Polynomial.C 8 * Polynomial.X ^ 2 + Polynomial.C 1 : Polynomial K).roots.toFinset.card ≤ 8 := by
    refine' le_trans ( Multiset.toFinset_card_le _ ) ( le_trans ( Polynomial.card_roots' _ ) _ );
    erw [ Polynomial.natDegree_add_C ] ; erw [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> erw [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> erw [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> simp +decide ;
    all_goals by_cases h : ( 7 : K ) = 0 <;> by_cases h' : ( 14 : K ) = 0 <;> by_cases h'' : ( 8 : K ) = 0 <;> simp +decide [ h, h', h'' ] ;
  refine' le_trans _ h_deg;
  refine Finset.card_le_card ?_;
  simp +decide [ Finset.subset_iff ];
  exact fun x hx₁ hx₂ => ⟨ ne_of_apply_ne ( Polynomial.eval 0 ) ( by simp +decide ), hx₁ ⟩

/-
PROBLEM
Lower bound: when a root exists in char ≠ 2,3, the filter has ≥ 8 elements.

PROVIDED SOLUTION
Given hroot: ∃ x₀ with octic(x₀)=0 and 2x₀²+1≠0. Obtain x₀.

Step 1: Establish x₀ properties.
- hx₀_ne : x₀ ≠ 0 (octic_root_ne_zero)
- hx₀_sq : x₀²+1 ≠ 0 (octic_root_sq_add_one_ne)

Step 2: Define θ = theta x₀, θ₂ = theta2 x₀ = theta (theta x₀), θ₃ = theta (theta (theta x₀)).
Using octic_root_preserved_by_theta iteratively:
- θ(x₀) is an octic root with 2θ(x₀)²+1≠0 and θ(x₀)≠0
- Apply again to θ(x₀) to get θ₂(x₀) is an octic root
- Apply again to get θ₃(x₀) is an octic root

Step 3: All negatives are also octic roots (octic_eval_neg).

Step 4: The filter contains {x₀, -x₀, θ(x₀), -θ(x₀), θ₂(x₀), -θ₂(x₀), θ₃(x₀), -θ₃(x₀)}.

Step 5: These 8 elements are distinct.
- x₀ ≠ -x₀ (char ≠ 2, x₀ ≠ 0): use two_ne_zero_of_ringChar_ne_two hchar2 and the fact that if x₀ = -x₀ then 2·x₀ = 0, so x₀ = 0.
- Similarly θ^k(x₀) ≠ -θ^k(x₀).
- The orbit {x₀, θ(x₀), θ₂(x₀), θ₃(x₀)} has 4 distinct elements because theta2 x₀ ≠ x₀ (from 2x₀²+1≠0 via theta2_eq_x_iff).
  More precisely: theta4 x₀ = x₀ (from fourth_iterate_factored), and if the orbit had < 4 elements, either theta x₀ = x₀ (impossible by theta_no_affine_fixed_point) or theta2 x₀ = x₀ (contradicts 2x₀²+1≠0).
- No θ^k(x₀) = -θ^j(x₀): If θ^k(x₀) = -θ^j(x₀), then θ^{k-j mod 4}(x₀) = -x₀. The cases:
  * θ²(x₀) = -x₀: by theta2_eq_neg_iff, 2x₀⁴+4x₀²+1=0, contradicting octic(x₀)=0 by octic_ne_zero_of_quartic_zero.
  * θ(x₀) = -x₀: then θ²(x₀) = θ(-x₀) = -θ(x₀) = x₀, so theta2 x₀ = x₀, contradicting 2x₀²+1≠0.
  * θ³(x₀) = -x₀: apply θ to get θ⁴(x₀) = θ(-x₀) = -θ(x₀). But θ⁴(x₀) = x₀. So x₀ = -θ(x₀), same as θ(x₀) = -x₀, already ruled out.

Step 6: The filter ⊇ {x₀, -x₀, θ(x₀), -θ(x₀), θ₂(x₀), -θ₂(x₀), θ₃(x₀), -θ₃(x₀)}, so card ≥ 8.

Use Finset.card_le_card to bound card ≥ |{the 8 elements}| = 8.
-/
set_option maxHeartbeats 3200000 in
lemma octic_nonperiod2_card_ge_8 (hchar2 : ringChar K ≠ 2) (hchar3 : ringChar K ≠ 3)
    (hsplit : ∃ i : K, i ^ 2 = -1)
    (hroot : ∃ x : K, x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1 = 0 ∧
      2 * x ^ 2 + 1 ≠ 0) :
    (Finset.univ.filter (fun x : K =>
      x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1 = 0 ∧
      2 * x ^ 2 + 1 ≠ 0)).card ≥ 8 := by
  revert hroot;
  intro h_exists_root
  obtain ⟨x₀, hx₀⟩ := h_exists_root
  set S := Finset.filter (fun x => x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1 = 0 ∧ 2 * x ^ 2 + 1 ≠ 0) (Finset.univ : Finset K) with hS_def

  have h_filter : S ⊇ {x₀, -x₀, theta x₀, -theta x₀, theta2 x₀, -theta2 x₀, theta3 x₀, -theta3 x₀} := by
    have h_filter : ∀ x ∈ ({x₀, theta x₀, theta2 x₀, theta3 x₀} : Finset K), x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1 = 0 ∧ 2 * x ^ 2 + 1 ≠ 0 := by
      have h_filter : theta x₀ ^ 8 + 7 * theta x₀ ^ 6 + 14 * theta x₀ ^ 4 + 8 * theta x₀ ^ 2 + 1 = 0 ∧ 2 * theta x₀ ^ 2 + 1 ≠ 0 ∧ theta x₀ ≠ 0 := by
        apply octic_root_preserved_by_theta hchar2 hchar3 (octic_root_ne_zero hx₀.left) (octic_root_sq_add_one_ne hx₀.left) hx₀.left hx₀.right
      have h_filter2 : theta2 x₀ ^ 8 + 7 * theta2 x₀ ^ 6 + 14 * theta2 x₀ ^ 4 + 8 * theta2 x₀ ^ 2 + 1 = 0 ∧ 2 * theta2 x₀ ^ 2 + 1 ≠ 0 ∧ theta2 x₀ ≠ 0 := by
        convert octic_root_preserved_by_theta hchar2 hchar3 _ _ _ _ using 1 ; aesop ( simp_config := { decide := true } ) ;
        · grind +ring;
        · exact h_filter.1;
        · exact h_filter.2.1
      have h_filter3 : theta3 x₀ ^ 8 + 7 * theta3 x₀ ^ 6 + 14 * theta3 x₀ ^ 4 + 8 * theta3 x₀ ^ 2 + 1 = 0 ∧ 2 * theta3 x₀ ^ 2 + 1 ≠ 0 ∧ theta3 x₀ ≠ 0 := by
        convert octic_root_preserved_by_theta hchar2 hchar3 _ _ _ _ using 1 ; aesop ( simp_config := { decide := true } ) ;
        · convert octic_root_sq_add_one_ne h_filter2.1 using 1;
        · exact h_filter2.1;
        · exact h_filter2.2.1
      aesop ( simp_config := { decide := true } ) ;
    simp_all +decide [ Finset.subset_iff ];
    grind +ring;
  have h_distinct : x₀ ≠ -x₀ ∧ x₀ ≠ theta x₀ ∧ x₀ ≠ -theta x₀ ∧ x₀ ≠ theta2 x₀ ∧ x₀ ≠ -theta2 x₀ ∧ x₀ ≠ theta3 x₀ ∧ x₀ ≠ -theta3 x₀ ∧ theta x₀ ≠ -theta x₀ ∧ theta x₀ ≠ theta2 x₀ ∧ theta x₀ ≠ -theta2 x₀ ∧ theta x₀ ≠ theta3 x₀ ∧ theta x₀ ≠ -theta3 x₀ ∧ theta2 x₀ ≠ -theta2 x₀ ∧ theta2 x₀ ≠ theta3 x₀ ∧ theta2 x₀ ≠ -theta3 x₀ ∧ theta3 x₀ ≠ -theta3 x₀ := by
    have h_distinct : x₀ ≠ -x₀ ∧ theta x₀ ≠ -theta x₀ ∧ theta2 x₀ ≠ -theta2 x₀ ∧ theta3 x₀ ≠ -theta3 x₀ := by
      have h_distinct : ∀ x : K, x ≠ 0 → x ≠ -x := by
        grind +suggestions;
      apply And.intro (h_distinct x₀ (by
      rintro rfl; norm_num at hx₀;)) (And.intro (h_distinct (theta x₀) (by
      by_contra h_contra
      have h_eq : x₀ ^ 2 = -1 := by
        exact eq_neg_of_add_eq_zero_left ( by rw [ theta_def ] at h_contra; linear_combination' h_contra * x₀ - inv_mul_cancel₀ ( show x₀ ≠ 0 from by rintro rfl; norm_num at hx₀ ) ) ;
      have h_contra : x₀ ^ 8 + 7 * x₀ ^ 6 + 14 * x₀ ^ 4 + 8 * x₀ ^ 2 + 1 = 0 := by
        exact hx₀.1
      have h_contra' : 2 * x₀ ^ 2 + 1 = 0 := by
        rw [ show x₀ ^ 8 = ( x₀ ^ 2 ) ^ 4 by ring, show x₀ ^ 6 = ( x₀ ^ 2 ) ^ 3 by ring, show x₀ ^ 4 = ( x₀ ^ 2 ) ^ 2 by ring, h_eq ] at h_contra ; ring_nf at h_contra ; aesop ( simp_config := { decide := true } ) ;
      exact hx₀.2 h_contra')) (And.intro (h_distinct (theta2 x₀) (by
      simp_all +decide [ Finset.subset_iff ];
      intro h; simp_all +decide [ theta2 ] ;)) (h_distinct (theta3 x₀) (by
      intro h; have := Finset.mem_filter.mp ( h_filter ( Finset.mem_insert_of_mem ( Finset.mem_insert_of_mem ( Finset.mem_insert_of_mem ( Finset.mem_insert_of_mem ( Finset.mem_insert_of_mem ( Finset.mem_insert_of_mem ( Finset.mem_insert_self _ _ ) ) ) ) ) ) ) ) ; simp_all +decide ;))))
    have h_orbit : x₀ ≠ theta x₀ ∧ x₀ ≠ theta2 x₀ ∧ x₀ ≠ theta3 x₀ ∧ theta x₀ ≠ theta2 x₀ ∧ theta x₀ ≠ theta3 x₀ ∧ theta2 x₀ ≠ theta3 x₀ := by
      have h_orbit : theta4 x₀ = x₀ := by
        convert fourth_iterate_factored ( show x₀ ≠ 0 from ?_ ) hchar2 using 1 <;> aesop ( simp_config := { decide := true } ) ;
      have h_orbit_distinct : theta x₀ ≠ x₀ ∧ theta2 x₀ ≠ x₀ ∧ theta3 x₀ ≠ x₀ ∧ theta2 x₀ ≠ theta x₀ ∧ theta3 x₀ ≠ theta x₀ ∧ theta3 x₀ ≠ theta2 x₀ := by
        have h_orbit_distinct : theta x₀ ≠ x₀ ∧ theta2 x₀ ≠ x₀ ∧ theta3 x₀ ≠ x₀ := by
          have h_orbit_distinct : theta x₀ ≠ x₀ ∧ theta2 x₀ ≠ x₀ := by
            exact ⟨ theta_no_affine_fixed_point ( show x₀ ≠ 0 from by rintro rfl; simp +decide at hx₀ ), by simpa [ * ] using theta2_eq_x_iff ( show x₀ ≠ 0 from by rintro rfl; simp +decide at hx₀ ) hchar2 |>.not.mpr hx₀.2 ⟩
          have h_orbit_distinct' : theta3 x₀ ≠ x₀ := by
            intro h; have := h_orbit; simp_all +decide [ theta4 ] ;
            unfold theta3 at h; simp_all +decide [ theta ] ;
          exact ⟨h_orbit_distinct.left, h_orbit_distinct.right, h_orbit_distinct'⟩
        have h_orbit_distinct' : theta2 x₀ ≠ theta x₀ ∧ theta3 x₀ ≠ theta x₀ ∧ theta3 x₀ ≠ theta2 x₀ := by
          refine' ⟨ _, _, _ ⟩ <;> intro h <;> simp_all +decide [ theta2, theta3, theta4 ]
        exact ⟨h_orbit_distinct.left, h_orbit_distinct.right.left, h_orbit_distinct.right.right, h_orbit_distinct'.left, h_orbit_distinct'.right.left, h_orbit_distinct'.right.right⟩
      exact ⟨by
      exact Ne.symm h_orbit_distinct.1, by
        exact Ne.symm h_orbit_distinct.2.1, by
        exact Ne.symm h_orbit_distinct.2.2.1, by
        exact Ne.symm h_orbit_distinct.2.2.2.1, by
        exact Ne.symm h_orbit_distinct.2.2.2.2.1, by
        exact Ne.symm h_orbit_distinct.2.2.2.2.2⟩
    have h_neg_orbit : x₀ ≠ -theta x₀ ∧ x₀ ≠ -theta2 x₀ ∧ x₀ ≠ -theta3 x₀ ∧ theta x₀ ≠ -theta2 x₀ ∧ theta x₀ ≠ -theta3 x₀ ∧ theta2 x₀ ≠ -theta3 x₀ := by
      have h_neg_orbit : theta2 x₀ ≠ -x₀ ∧ theta x₀ ≠ -x₀ ∧ theta3 x₀ ≠ -x₀ := by
        have h_neg_orbit : theta2 x₀ ≠ -x₀ := by
          have h_neg_orbit : theta2 x₀ ≠ -x₀ := by
            intro h
            have h_eq : 2 * x₀ ^ 4 + 4 * x₀ ^ 2 + 1 = 0 := by
              convert theta2_eq_neg_iff _ _ _ |>.1 h using 1 <;> ring! ; aesop ( simp_config := { decide := true } ) ;
              · exact hchar2;
              · grind +splitImp
            exact absurd ( octic_ne_zero_of_quartic_zero hchar2 hchar3 h_eq ) ( by aesop )
          exact h_neg_orbit
        have h_neg_orbit' : theta x₀ ≠ -x₀ := by
          intro h_neg_orbit'
          have h_contra : 2 * x₀ ^ 2 + 1 = 0 := by
            unfold theta at h_neg_orbit';
            linear_combination' h_neg_orbit' * x₀ - inv_mul_cancel₀ ( show x₀ ≠ 0 from by aesop_cat )
          exact hx₀.right h_contra
        have h_neg_orbit'' : theta3 x₀ ≠ -x₀ := by
          intro h_neg_orbit'';
          have h_neg_orbit''' : theta4 x₀ = -theta x₀ := by
            convert congr_arg theta h_neg_orbit'' using 1;
            unfold theta; ring;
          have h_neg_orbit'''' : theta4 x₀ = x₀ := by
            have := fourth_iterate_factored ( show x₀ ≠ 0 from by rintro rfl; norm_num at hx₀ ) hchar2; simp_all +decide ;
          have h_neg_orbit''''' : x₀ = -theta x₀ := by
            rw [ ← h_neg_orbit''', h_neg_orbit'''' ]
          have h_neg_orbit'''''' : theta x₀ = -x₀ := by
            linear_combination' h_neg_orbit'''''
          exact h_neg_orbit' h_neg_orbit''''''
        exact ⟨h_neg_orbit, h_neg_orbit', h_neg_orbit''⟩;
      have h_neg_orbit : theta x₀ ≠ -theta2 x₀ ∧ theta x₀ ≠ -theta3 x₀ ∧ theta2 x₀ ≠ -theta3 x₀ := by
        have h_neg_orbit : theta4 x₀ = x₀ := by
          exact fourth_iterate_factored ( show x₀ ≠ 0 from by rintro rfl; norm_num at hx₀ ) hchar2 |>.2 ( by aesop ) |> fun h => by aesop;
        have h_neg_orbit : theta3 x₀ ≠ -theta x₀ := by
          intro h
          have h_contra : theta4 x₀ = -theta2 x₀ := by
            exact theta_neg_eq _ ( show theta x₀ ≠ 0 from by
                                    grind +ring ) ▸ h ▸ rfl
          have h_contra' : x₀ = -theta2 x₀ := by
            rw [←h_contra, h_neg_orbit]
          have h_contra'' : theta2 x₀ = -x₀ := by
            exact eq_neg_of_add_eq_zero_right ( by linear_combination' h_contra' )
          exact absurd h_contra'' (by
          exact fun h => ‹theta2 x₀ ≠ -x₀ ∧ theta x₀ ≠ -x₀ ∧ theta3 x₀ ≠ -x₀›.1 h)
        have h_neg_orbit : theta2 x₀ ≠ -theta3 x₀ := by
          intro h_neg_orbit
          have h_contra : x₀ = -theta x₀ := by
            have h_contra : theta (theta2 x₀) = -theta (theta3 x₀) := by
              unfold theta; simp +decide [ h_neg_orbit ] ; ring;
            have h_contra : theta3 x₀ = -theta4 x₀ := by
              exact h_contra ▸ by rfl;
            have h_contra : theta3 x₀ = -x₀ := by
              rw [h_contra, ‹theta4 x₀ = x₀›]
            have h_contra : x₀ = -theta x₀ := by
              grind +extAll
            exact h_contra.symm ▸ by
              grind +ring
          exact h_orbit.right.right.right.right.left (by
          grind)
        exact ⟨by
        intro h
        have h_contra : theta4 x₀ = -theta x₀ := by
          have h_contra : theta (theta x₀) = -theta (theta2 x₀) := by
            rw [h] at *; simp_all +decide [ theta_def ] ;
            ring
          have h_contra : theta2 x₀ = -theta3 x₀ := by
            exact h_contra.trans ( by rfl ) |> Eq.trans <| by rfl;
          have h_contra : theta3 x₀ = -theta4 x₀ := by
            grobner
          have h_contra : theta4 x₀ = -theta x₀ := by
            grind +ring
          exact h_contra
        have h_contra : x₀ = -theta x₀ := by
          rw [←h_contra, ‹theta4 x₀ = x₀›]
        have h_contra : theta x₀ = -x₀ := by
          exact eq_neg_of_add_eq_zero_left ( by linear_combination' h_contra )
        exact h_neg_orbit (by
        grind), by
          grobner, by
          exact h_neg_orbit⟩;
      grind +ring;
    grind +ring;
  refine' le_trans _ ( Finset.card_mono h_filter );
  grind +splitImp

/-! ### Corrected sorry lemmas -/

/-- Number of roots of the octic that are NOT period-2 equals 0 or 8.
    The original statement was missing `hchar3`; in char 3, the octic equals
    the quartic squared, giving 4 non-period-2 roots (not 0 or 8). -/
lemma octic_nonperiod2_root_card (hchar2 : ringChar K ≠ 2) (hchar3 : ringChar K ≠ 3)
    (hsplit : ∃ i : K, i ^ 2 = -1) :
    (Finset.univ.filter (fun x : K =>
      x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1 = 0 ∧
      2 * x ^ 2 + 1 ≠ 0)).card =
    if (∃ x : K, x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1 = 0 ∧
        2 * x ^ 2 + 1 ≠ 0) then 8 else 0 := by
  split_ifs with h
  · exact le_antisymm octic_nonperiod2_card_le_8 (octic_nonperiod2_card_ge_8 hchar2 hchar3 hsplit h)
  · simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies]
    intro x hx; exact absurd ⟨x, hx⟩ h

/-! ## Part 5: Existence criteria for the combined octic non-period-2 roots -/

/-
PROBLEM
The octic has a non-period-2 root iff q ≡ 1 mod 60.
    The original statement was missing `hchar3`; see `octic_ne_zero_of_quartic_zero`.

PROVIDED SOLUTION
Split into forward and backward.

Forward: Given ⟨x, hoct, h2⟩. Then char ≠ 5 (by char_ne_5_of_octic_nonperiod2). Also x ≠ 0 (since octic(0)=1≠0). By octic_root_iff_m60_root.mp ⟨x, hx_ne, hoct⟩, get ⟨v, hv⟩ with m60(v)=0. Then use mod60_of_m60_root hchar2 hchar3 (char_ne_5_of_octic_nonperiod2 hoct h2) hsplit ⟨v, hv⟩.

Backward: Given hmod : q % 60 = 1. By m60_root_of_mod60 hmod, get ⟨v, hv⟩. By octic_root_iff_m60_root.mpr ⟨v, hv⟩, get ⟨x, hx_ne, hoct⟩. Since q%60=1 implies 5|q-1, and in char 5 we'd have 5∤q-1 (since q=5^k, 5^k-1 ≡ 4 mod 5), so char ≠ 5. Then octic_root_period2_coprime hchar2 (char≠5) hoct gives 2x²+1≠0.
-/
lemma octic_nonperiod2_exists_iff_mod60 (hchar2 : ringChar K ≠ 2) (hchar3 : ringChar K ≠ 3)
    (hsplit : ∃ i : K, i ^ 2 = -1) :
    (∃ x : K, x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1 = 0 ∧
      2 * x ^ 2 + 1 ≠ 0) ↔ Fintype.card K % 60 = 1 := by
  by_cases hchar5 : ringChar K = 5;
  · -- In characteristic 5, the octic polynomial factors as $(2x^2 + 1)^4 = 0$.
    have h_factor : ∀ x : K, x^8 + 7 * x^6 + 14 * x^4 + 8 * x^2 + 1 = (2 * x^2 + 1)^4 := by
      intro x
      ring;
      have := hchar5 ▸ ringChar.spec K 5; simp_all +decide [ pow_succ, mul_assoc ] ;
      grind +ring;
    simp_all +decide [ pow_succ ];
    have := FiniteField.card K ( ringChar K ) ; simp_all +decide ;
    rcases this with ⟨ n, hn ⟩ ; rw [ hn ] ; rcases n with ( _ | _ | n ) <;> norm_num [ Nat.pow_succ', ← mul_assoc, Nat.mul_mod ] at *;
    · contradiction;
    · exact ne_of_apply_ne ( · % 5 ) ( by norm_num [ Nat.mul_mod, Nat.pow_mod ] );
  · constructor <;> intro hmod;
    · obtain ⟨ x, hx ⟩ := hmod;
      obtain ⟨ v, hv ⟩ := octic_root_iff_m60_root hchar2 hsplit |>.1 ⟨ x, by aesop_cat, hx.1 ⟩ ; exact mod60_of_m60_root hchar2 hchar3 hchar5 hsplit ⟨ v, hv ⟩ ;
    · -- By `octic_root_iff_m60_root`, we know that if `m60` has a root, then `octic` also has a root.
      obtain ⟨v, hv⟩ : ∃ v : K, v^8 - 7 * v^6 + 14 * v^4 - 8 * v^2 + 1 = 0 := m60_root_of_mod60 hmod
      obtain ⟨x, hx⟩ : ∃ x : K, x^8 + 7 * x^6 + 14 * x^4 + 8 * x^2 + 1 = 0 ∧ x ≠ 0 := by
        have := octic_root_iff_m60_root hchar2 hsplit |>.2 ⟨ v, hv ⟩ ; aesop;
      exact ⟨ x, hx.1, octic_root_period2_coprime hchar2 hchar5 hx.1 ⟩

/-! ## Part 6: Assembly — the four-cycle count -/

/-
PROBLEM
The genuine 4-cycle filter decomposes into quartic and octic contributions.
    The original statement was missing `hchar3`; in char 3, quartic and octic
    roots overlap, making the sum overcount.

PROVIDED SOLUTION
The key decomposition: {x≠0, theta4 x=x, theta2 x≠x} = {2x⁴+4x²+1=0} ∪ {octic=0, 2x²+1≠0} (disjoint union).

Step 1: Show the LHS filter equals the union of the two RHS filters.
For any x in the LHS: x≠0, theta4 x=x, theta2 x≠x. By fourth_iterate_factored: (2x²+1)(2x⁴+4x²+1)(octic)=0. By theta2_eq_x_iff: 2x²+1≠0. So (2x⁴+4x²+1)(octic)=0, meaning either 2x⁴+4x²+1=0 or octic=0.
Conversely: if 2x⁴+4x²+1=0, then x≠0 (quartic_ne_zero_at_zero), 2x²+1≠0 (quartic_root_not_period2), and the product (2x²+1)(2x⁴+4x²+1)(octic)=0, so theta4 x=x. theta2 x≠x from 2x²+1≠0.
If octic=0 and 2x²+1≠0, then x≠0 (octic_ne_zero_at_zero), the product=0, theta4 x=x, theta2 x≠x.

Step 2: Disjointness: if 2x⁴+4x²+1=0, then octic≠0 (by octic_ne_zero_of_quartic_zero with char≠3). And quartic roots trivially have 2x²+1≠0 (quartic_root_not_period2). So the quartic set ∩ {octic=0,2x²+1≠0} = ∅.

Step 3: Use Finset.filter_union_filter_neg_eq or card_union_of_disjoint to get the sum.

Concretely: convert the LHS to a filter over the disjunction, split into a disjoint union, use Finset.card_union_of_disjoint.
-/
lemma four_cycle_filter_card_eq (hchar2 : ringChar K ≠ 2) (hchar3 : ringChar K ≠ 3)
    (hsplit : ∃ i : K, i ^ 2 = -1) :
    (Finset.univ.filter (fun x : K =>
      x ≠ 0 ∧ theta4 x = x ∧ theta2 x ≠ x)).card =
    (Finset.univ.filter (fun x : K => 2 * x ^ 4 + 4 * x ^ 2 + 1 = 0)).card +
    (Finset.univ.filter (fun x : K =>
      x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1 = 0 ∧
      2 * x ^ 2 + 1 ≠ 0)).card := by
  rw [ ← Finset.card_union_of_disjoint ];
  · refine' congr_arg Finset.card ( Finset.ext fun x => _ );
    by_cases hx : x = 0 <;> simp +decide [ hx, fourth_iterate_factored, theta2_eq_x_iff, hchar2 ];
    grind +ring;
  · simp +contextual [ Finset.disjoint_left ];
    intro x hx₁ hx₂; have := octic_ne_zero_of_quartic_zero hchar2 hchar3 hx₁; simp_all +decide ;

/-! ## Part 7: Assembly of the four-cycle count formula -/

/-
PROBLEM
The quartic root count equals 4 if q ≡ 1 mod 16, else 0.

PROVIDED SOLUTION
Combine quartic_root_card (which gives card = if exists then 4 else 0) with quartic_root_iff_m16_root and m16_root_iff_mod16.

Specifically:
1. quartic_root_card gives: filter card = if (∃ x, 2x⁴+4x²+1=0) then 4 else 0
2. quartic_root_iff_m16_root gives: (∃ x≠0, quartic=0) ↔ (∃ u, m16(u)=0)
3. m16_root_iff_mod16 gives: (∃ u, m16(u)=0) ↔ q%16=1
4. quartic_ne_zero_at_zero gives: quartic(0) ≠ 0, so (∃ x, quartic=0) ↔ (∃ x≠0, quartic=0)

Chain: (∃ x, quartic=0) ↔ (∃ x≠0, quartic=0) ↔ (∃ u, m16=0) ↔ q%16=1

Then rw quartic_root_card, and congr on the if condition.
-/
lemma quartic_root_count_mod16 (hchar2 : ringChar K ≠ 2)
    (hsplit : ∃ i : K, i ^ 2 = -1) :
    (Finset.univ.filter (fun x : K => 2 * x ^ 4 + 4 * x ^ 2 + 1 = 0)).card =
    if Fintype.card K % 16 = 1 then 4 else 0 := by
  split_ifs with hmod16 hmod16 <;> simp_all +decide only [card_filter];
  · obtain ⟨ u, hu ⟩ := m16_root_iff_mod16 hchar2 hsplit |>.2 hmod16; simp_all +decide [ Finset.sum_ite ] ;
    exact quartic_root_card hchar2 |> fun h => h.trans ( if_pos <| by obtain ⟨ x, hx ⟩ := quartic_root_iff_m16_root hchar2 hsplit |>.2 ⟨ u, hu ⟩ ; exact ⟨ x, hx.2 ⟩ );
  · -- By combining the results from quartic_root_iff_m16_root and m16_root_iff_mod16, we can conclude that if there's no root of the quartic equation, then there's no root of m16.
    have h_no_root_m16 : ¬(∃ u : K, u ^ 4 - 4 * u ^ 2 + 2 = 0) := by
      exact fun ⟨ u, hu ⟩ => hmod16 <| m16_root_iff_mod16 hchar2 hsplit |>.1 ⟨ u, hu ⟩;
    contrapose! h_no_root_m16 with h_no_root_m16' ; simp_all +decide [ Finset.sum_ite ] ; (
    exact quartic_root_iff_m16_root hchar2 hsplit |>.1 ⟨ _, h_no_root_m16'.choose_spec |> fun h => by
      intro H; simp +decide [ H ] at h;, h_no_root_m16'.choose_spec ⟩);

/-
PROBLEM
The octic non-period-2 root count equals 8 if q ≡ 1 mod 60, else 0 (char ≠ 3).

PROVIDED SOLUTION
Combine octic_nonperiod2_root_card (which gives card = if exists then 8 else 0) with octic_nonperiod2_exists_iff_mod60.

1. octic_nonperiod2_root_card gives: filter card = if (∃ x, octic=0 ∧ 2x²+1≠0) then 8 else 0
2. octic_nonperiod2_exists_iff_mod60 gives: (∃ x, octic=0 ∧ 2x²+1≠0) ↔ q%60=1

So just rewrite the if condition.
-/
lemma octic_nonperiod2_count_mod60 (hchar2 : ringChar K ≠ 2) (hchar3 : ringChar K ≠ 3)
    (hsplit : ∃ i : K, i ^ 2 = -1) :
    (Finset.univ.filter (fun x : K =>
      x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1 = 0 ∧
      2 * x ^ 2 + 1 ≠ 0)).card =
    if Fintype.card K % 60 = 1 then 8 else 0 := by
  convert octic_nonperiod2_root_card hchar2 hchar3 hsplit using 2;
  exact?

/-
PROBLEM
In char 3, the octic equals the quartic squared.

PROVIDED SOLUTION
In char 3: 7≡1, 14≡2, 8≡2, and (2x⁴+4x²+1)² = 4x⁸+16x⁶+12x⁴+8x²+1. In char 3: 4≡1, 16≡1, 12≡0. So (2x⁴+4x²+1)² = x⁸+x⁶+0+8x²+1. Wait, let me recompute: (2x⁴+4x²+1)² = 4x⁸+16x⁶+4x⁴+16x⁴+8x²+1... actually let me just do it properly.

(2x⁴+4x²+1)² = 4x⁸ + 2·2x⁴·4x² + 2·2x⁴·1 + 16x⁴ + 2·4x²·1 + 1
= 4x⁸ + 16x⁶ + 4x⁴ + 16x⁴ + 8x² + 1
= 4x⁸ + 16x⁶ + 20x⁴ + 8x² + 1

In char 3: 4≡1, 16≡1, 20≡2. So = x⁸ + x⁶ + 2x⁴ + 2x² + 1.
And the octic in char 3: 7≡1, 14≡2, 8≡2. So = x⁸ + x⁶ + 2x⁴ + 2x² + 1. ✓

Use: have h3K : (3:K) = 0 from CharP and ringChar. Then show each coefficient difference is divisible by 3. The difference between LHS and RHS is a polynomial identity that becomes 0 when (3:K) = 0. Use ring to show LHS - RHS = 3*(something), then use h3K.
-/
lemma octic_eq_quartic_sq_char3 (hchar3 : ringChar K = 3) (x : K) :
    x ^ 8 + 7 * x ^ 6 + 14 * x ^ 4 + 8 * x ^ 2 + 1 =
    (2 * x ^ 4 + 4 * x ^ 2 + 1) ^ 2 := by
  have h_char3 : (3 : K) = 0 := by
    rw [ ← Nat.cast_ofNat, ← hchar3, ringChar.spec ];
  grind

/-
PROBLEM
In char 3 with q ≡ 1 mod 4, q % 60 ≠ 1.

PROVIDED SOLUTION
If ringChar K = 3, then q = 3^n for some n. Since 3 | q, we have q % 3 = 0. But if q % 60 = 1, then q % 3 = 1 (since 3 | 60 implies q%3 = (q%60)%3 = 1%3 = 1). This contradicts q % 3 = 0.

Concretely: use FiniteField.card to get q = 3^n. Then 3 | q since n ≥ 1 (from Fintype.one_lt_card). So q % 3 = 0. If q % 60 = 1, then q ≡ 1 mod 3 (since 3|60), contradiction.
-/
lemma q_mod60_ne_1_of_char3 (hchar3 : ringChar K = 3)
    (hsplit : ∃ i : K, i ^ 2 = -1) :
    Fintype.card K % 60 ≠ 1 := by
  -- Since $K$ is a finite field of characteristic $3$, we have $Fintype.card K = 3^n$ for some $n$.
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card K = 3^n := by
    have := FiniteField.card K ( ringChar K ) ; aesop;
  rcases n with ( _ | _ | n ) <;> simp_all +decide [ pow_succ' ];
  · exact absurd hn ( Nat.ne_of_gt ( Fintype.one_lt_card ) );
  · omega

/-
PROBLEM
In char 3, the 4-cycle filter equals the quartic root filter.

PROVIDED SOLUTION
In char 3, we show the two filters are equal (element-wise). For any x:

Forward: x≠0 ∧ theta4 x = x ∧ theta2 x ≠ x → 2x⁴+4x²+1=0

By fourth_iterate_factored: theta4 x = x ↔ (2x²+1)(2x⁴+4x²+1)(octic) = 0.
By theta2_eq_x_iff: theta2 x ≠ x → 2x²+1 ≠ 0.
By octic_eq_quartic_sq_char3: octic = quartic². So the product becomes (2x²+1)(quartic)³ = 0.
Since 2x²+1 ≠ 0, we get quartic = 0.

Backward: 2x⁴+4x²+1 = 0 → x≠0 ∧ theta4 x = x ∧ theta2 x ≠ x

x≠0: by quartic_ne_zero_at_zero (evaluating at 0 gives 1≠0).
2x²+1≠0: by quartic_root_not_period2.
theta2 x ≠ x: by theta2_eq_x_iff, since 2x²+1≠0.
theta4 x = x: by fourth_iterate_factored, since (2x²+1)(quartic)(octic) = (2x²+1)·0·octic = 0.

Use Finset.ext and then prove the biconditional for each x.
-/
lemma four_cycle_filter_char3 (hchar2 : ringChar K ≠ 2) (hchar3 : ringChar K = 3)
    (hsplit : ∃ i : K, i ^ 2 = -1) :
    (Finset.univ.filter (fun x : K =>
      x ≠ 0 ∧ theta4 x = x ∧ theta2 x ≠ x)).card =
    (Finset.univ.filter (fun x : K => 2 * x ^ 4 + 4 * x ^ 2 + 1 = 0)).card := by
  refine' Finset.card_bij ( fun x hx => x ) _ _ _ <;> simp_all +decide [ Finset.ext_iff, forall_const ];
  · intro x hx hx' hx''; have := fourth_iterate_factored hx ( by aesop ) ; simp_all +decide [ sub_eq_iff_eq_add ] ;
    rcases hx' with ( ( hx' | hx' ) | hx' ) <;> simp_all +decide [ theta2_eq_x_iff ];
    have := octic_eq_quartic_sq_char3 hchar3 x; simp_all +decide [ sub_eq_iff_eq_add ] ;
  · intro b hb
    have hb_ne_zero : b ≠ 0 := by
      rintro rfl; norm_num at hb;
    have hb_four_cycle : theta4 b = b := by
      rw [ fourth_iterate_factored hb_ne_zero ];
      · grind;
      · aesop
    have hb_two_cycle : theta2 b ≠ b := by
      have hb_two_cycle : 2 * b ^ 2 + 1 ≠ 0 := by
        grind +revert
      simp_all +decide [ theta2_eq_x_iff ]
    exact ⟨hb_ne_zero, hb_four_cycle, hb_two_cycle⟩

/-
PROBLEM
**Four-cycle count formula** (split case q ≡ 1 mod 4).
Let N₄ be the number of genuine affine 4-cycles. Then
  N₄ = 𝟙[q ≡ 1 (mod 16)] + 2 · 𝟙[q ≡ 1 (mod 60)].

PROVIDED SOLUTION
Split into two cases: ringChar K = 3 vs ringChar K ≠ 3.

Case 1 (ringChar K = 3):
By four_cycle_filter_char3: N = quartic_count.
By quartic_root_count_mod16: quartic_count = if q%16=1 then 4 else 0.
By q_mod60_ne_1_of_char3: q%60 ≠ 1.
So N/4 = (if q%16=1 then 4 else 0)/4 = (if q%16=1 then 1 else 0).
And RHS = (if q%16=1 then 1 else 0) + 2*0 = (if q%16=1 then 1 else 0). ✓

Case 2 (ringChar K ≠ 3):
By four_cycle_filter_card_eq: N = quartic_count + octic_count.
By quartic_root_count_mod16: quartic_count = if q%16=1 then 4 else 0.
By octic_nonperiod2_count_mod60: octic_count = if q%60=1 then 8 else 0.
So N = (if q%16=1 then 4 else 0) + (if q%60=1 then 8 else 0).
N/4 = ((if q%16=1 then 4 else 0) + (if q%60=1 then 8 else 0))/4.
This equals (if q%16=1 then 1 else 0) + 2*(if q%60=1 then 1 else 0).
The arithmetic: split on both conditions. (0+0)/4=0, (4+0)/4=1, (0+8)/4=2, (4+8)/4=3. And 0+0=0, 1+0=1, 0+2=2, 1+2=3. ✓

Split into two cases: by_cases hchar3 : ringChar K = 3.

Case 1 (ringChar K = 3):
- rw [four_cycle_filter_char3 hchar2 hchar3 hsplit] to replace filter with quartic filter
- rw [quartic_root_count_mod16 hchar2 hsplit] to get the if-then-else
- have hmod60 := q_mod60_ne_1_of_char3 hchar3 hsplit, use simp [hmod60] to simplify
- split_ifs and norm_num

Case 2 (ringChar K ≠ 3):
- rw [four_cycle_filter_card_eq hchar2 hchar3 hsplit] to decompose
- rw [quartic_root_count_mod16 hchar2 hsplit] to get first term
- rw [octic_nonperiod2_count_mod60 hchar2 hchar3 hsplit] to get second term
- split_ifs and norm_num/omega
-/
theorem four_cycle_count_formula' (hchar2 : ringChar K ≠ 2)
    (hsplit : ∃ i : K, i ^ 2 = -1) :
    (Finset.univ.filter (fun x : K =>
      x ≠ 0 ∧ theta4 x = x ∧ theta2 x ≠ x)).card / 4 =
    (if (Fintype.card K) % 16 = 1 then 1 else 0) +
    2 * (if (Fintype.card K) % 60 = 1 then 1 else 0) := by
  by_cases hchar3 : ringChar K = 3;
  · have hq_mod60_ne_1_of_char3 : Fintype.card K % 60 ≠ 1 :=
      q_mod60_ne_1_of_char3 hchar3 hsplit;
    rw [ four_cycle_filter_char3 hchar2 hchar3 hsplit, quartic_root_count_mod16 hchar2 hsplit ] ; aesop;
  · rw [ four_cycle_filter_card_eq hchar2 hchar3 hsplit, quartic_root_count_mod16 hchar2 hsplit, octic_nonperiod2_count_mod60 hchar2 hchar3 hsplit ] ; split_ifs <;> norm_num

end