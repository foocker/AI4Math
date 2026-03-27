/-
# Generalization of Example 7.21 to Arbitrary Degree (Remark 7.22)

We prove that the statement of Example 7.21 holds for polynomials of arbitrary degree d ≥ 1,
answering the question raised in Remark 7.22 affirmatively.

The proof is formalized at the level of integer sequences, axiomatizing the closure properties
of thick tensor ideals. The core mathematical argument — an induction using forward finite
differences and p-fold splitting — is fully formalized.

## Main Result

`all_powers_in_T`: Given a predicate `T` on `ℕ → ℕ` sequences satisfying the `SeqClosure`
axioms and containing the sequence `i ↦ i^d` for some `d ≥ 1`, the predicate `T` also
contains `i ↦ i^k` for all `k ≤ d`. This implies the full generalization of Example 7.21
to degree-d polynomials.
-/

import Mathlib

namespace Remark722

open Finset Nat

/-! ## Part 1: Integer-Valued Forward Differences -/

/-- Forward difference of an integer-valued sequence -/
def seqDelta (f : ℕ → ℤ) : ℕ → ℤ := fun i => f (i + 1) - f i

/-- Iterated forward difference -/
def seqDeltaIter (m : ℕ) (f : ℕ → ℤ) : ℕ → ℤ := seqDelta^[m] f

@[simp] lemma seqDeltaIter_zero (f : ℕ → ℤ) : seqDeltaIter 0 f = f := rfl

lemma seqDeltaIter_succ (m : ℕ) (f : ℕ → ℤ) :
    seqDeltaIter (m + 1) f = seqDelta (seqDeltaIter m f) :=
  Function.iterate_succ_apply' _ _ _

/-- The forward difference of `i^n` equals `Σ_{k<n} C(n,k) · i^k`.
    This follows from the binomial theorem. -/
lemma seqDelta_pow (n : ℕ) (i : ℕ) :
    seqDelta (fun k => (k : ℤ) ^ n) i =
    ∑ k ∈ range n, (n.choose k : ℤ) * (i : ℤ) ^ k := by
  simp +decide [seqDelta, add_pow]
  simp +decide [mul_comm, Finset.sum_range_succ]

/-! ## Part 2: Coefficient Analysis via `deltaCoeff`

We define `deltaCoeff d m j` as the coefficient of `i^j` when expanding
`Δ^m(i^d)` as a polynomial. The key properties are:
- The evaluation formula (`seqDeltaIter_eq_sum`)
- The leading coefficient equals `d.descFactorial m` (`deltaCoeff_leading`)
- All coefficients are natural numbers, ensuring non-negativity (`seqDeltaIter_nonneg`)
-/

/-- Coefficient of `i^j` when expanding `Δ^m(i^d)` as a polynomial.
    Defined recursively: applying `Δ` transforms each monomial `c · i^l` into
    `Σ_{j<l} c · C(l,j) · i^j`. -/
def deltaCoeff (d : ℕ) : ℕ → ℕ → ℕ
  | 0, j => if j = d then 1 else 0
  | m + 1, j => ∑ l ∈ range (d + 1),
      if j < l then deltaCoeff d m l * l.choose j else 0

/-- The evaluation formula: `Δ^m(i^d) = Σ_{j ≤ d} deltaCoeff d m j · i^j` -/
lemma seqDeltaIter_eq_sum (d m : ℕ) (hm : m ≤ d) (i : ℕ) :
    seqDeltaIter m (fun n => (n : ℤ) ^ d) i =
    ∑ j ∈ range (d + 1), (deltaCoeff d m j : ℤ) * (i : ℤ) ^ j := by
  induction' m with m ih generalizing i d
  · unfold seqDeltaIter deltaCoeff; aesop
  · have h_forward_diff : seqDeltaIter (m + 1) (fun n => (n : ℤ) ^ d) i =
        (∑ j ∈ Finset.range (d + 1), (deltaCoeff d m j : ℤ) * (i + 1) ^ j) -
        (∑ j ∈ Finset.range (d + 1), (deltaCoeff d m j : ℤ) * i ^ j) := by
      rw [seqDeltaIter_succ, seqDelta]
      exact congrArg₂ _ (mod_cast ih d (Nat.le_of_succ_le hm) (i + 1))
        (mod_cast ih d (Nat.le_of_succ_le hm) i)
    have h_delta_coeff : ∀ j ∈ Finset.range (d + 1),
        (deltaCoeff d (m + 1) j : ℤ) =
        ∑ l ∈ Finset.range (d + 1),
          (deltaCoeff d m l : ℤ) * (l.choose j : ℤ) * (if j < l then 1 else 0) := by
      intro j hj; norm_cast; aesop
    have h_interchange :
        ∑ j ∈ Finset.range (d + 1),
          (∑ l ∈ Finset.range (d + 1),
            (deltaCoeff d m l : ℤ) * (l.choose j : ℤ) * (if j < l then 1 else 0)) *
          (i : ℤ) ^ j =
        ∑ l ∈ Finset.range (d + 1), (deltaCoeff d m l : ℤ) *
          (∑ j ∈ Finset.range l, (l.choose j : ℤ) * (i : ℤ) ^ j) := by
      simp +decide [Finset.sum_mul _ _ _, mul_assoc, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp +decide [Finset.sum_ite]
      congr! 2
      grind
    simp_all +decide [Finset.sum_mul _ _ _]
    convert h_interchange.symm using 1
    · rw [← Finset.sum_sub_distrib]; refine' Finset.sum_congr rfl fun x hx => _
      rw [add_pow]
      simp +decide [mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _]
      simp +decide [Finset.sum_range_succ]
    · exact Finset.sum_congr rfl fun x hx => by
        rw [h_delta_coeff x (Finset.mem_range_succ_iff.mp hx)]
        simp +decide [Finset.sum_mul _ _ _]

/-- The leading coefficient: `deltaCoeff d m (d - m) = d.descFactorial m` -/
lemma deltaCoeff_leading (d m : ℕ) (hm : m ≤ d) :
    deltaCoeff d m (d - m) = d.descFactorial m := by
  induction' m with m ih generalizing d <;> simp_all +decide [Nat.descFactorial_succ]
  · exact if_pos rfl
  · rw [Nat.sub_succ'] at *; simp_all +decide [deltaCoeff]
    rw [Finset.sum_eq_single (d - m)]
    · rw [if_pos (Nat.sub_lt (Nat.sub_pos_of_lt hm) zero_lt_one), ih d hm.le,
        Nat.choose_symm (Nat.sub_pos_of_lt hm)]; ring
      norm_num [Nat.choose_one_right]
    · intro b hb hne; split_ifs <;> simp_all +decide []
      have h_delta_zero : ∀ d m j, m ≤ d → d - m < j → deltaCoeff d m j = 0 := by
        intros d m j hm hj
        induction' m with m ih generalizing d j <;> simp_all +decide []
        · exact if_neg (by linarith)
        · rw [deltaCoeff]; simp_all +decide []
          exact fun i hi hj => Or.inl <| ih d i (by linarith) <| by omega
      exact Or.inl (h_delta_zero d m b (by linarith) (by omega))
    · exact fun h => False.elim <| h <| Finset.mem_range.mpr <| Nat.lt_succ_of_le <| Nat.sub_le _ _

/-- Coefficients above degree `d - m` are zero -/
lemma deltaCoeff_eq_zero (d m j : ℕ) (hm : m ≤ d) (hj : d - m < j) :
    deltaCoeff d m j = 0 := by
  induction' m with m ih generalizing d j
  · exact if_neg (by aesop)
  · rw [deltaCoeff]
    simp +zetaDelta at *
    exact fun i hi₁ hi₂ => Or.inl <| ih d i (by linarith) <| by omega

/-- Non-negativity of `Δ^m(i^d)` for `m ≤ d`: since all `deltaCoeff` values are
    natural numbers (hence ≥ 0) and `i ≥ 0`, the sum is non-negative. -/
lemma seqDeltaIter_nonneg (d m : ℕ) (hm : m ≤ d) (i : ℕ) :
    0 ≤ seqDeltaIter m (fun n => (n : ℤ) ^ d) i := by
  have h_sum := seqDeltaIter_eq_sum d m hm i
  exact h_sum.symm ▸ Finset.sum_nonneg fun _ _ =>
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)

/-- `d.descFactorial (d - k) ≥ 2` when `1 ≤ k ≤ d - 1` and `d ≥ 2` -/
lemma descFactorial_ge_two (d k : ℕ) (hd : 2 ≤ d) (hk1 : 1 ≤ k) (hk2 : k ≤ d - 1) :
    2 ≤ d.descFactorial (d - k) := by
  rw [Nat.descFactorial_eq_prod_range]
  exact le_trans (by omega)
    (Finset.single_le_prod' (fun x hx => Nat.one_le_iff_ne_zero.mpr <|
      Nat.sub_ne_zero_of_lt <| by
        linarith [Finset.mem_range.mp hx,
          Nat.sub_add_cancel (show k ≤ d from hk2.trans (Nat.pred_le d))])
    (Finset.mem_range.mpr (Nat.sub_pos_of_lt <| by omega)))

/-! ## Part 3: Connecting ℤ and ℕ Forward Differences -/

/-- The ℕ-valued sequence from the m-th forward difference of `i^d`. -/
noncomputable def deltaSeq (d m : ℕ) : ℕ → ℕ :=
  fun i => (seqDeltaIter m (fun n => (n : ℤ) ^ d) i).toNat

/-- `deltaSeq` agrees with the integer version -/
lemma deltaSeq_coe (d m : ℕ) (hm : m ≤ d) (i : ℕ) :
    (deltaSeq d m i : ℤ) = seqDeltaIter m (fun n => (n : ℤ) ^ d) i :=
  Int.toNat_of_nonneg (seqDeltaIter_nonneg d m hm i)

/-- `deltaSeq d 0 i = i ^ d` -/
lemma deltaSeq_zero (d : ℕ) (i : ℕ) : deltaSeq d 0 i = i ^ d := by
  unfold deltaSeq; aesop

/-- `deltaSeq d m` is non-decreasing for `m < d` -/
lemma deltaSeq_mono (d m : ℕ) (hm : m < d) (i : ℕ) :
    deltaSeq d m i ≤ deltaSeq d m (i + 1) := by
  have h_eq : ↑(deltaSeq d m i) = seqDeltaIter m (fun n => (n : ℤ) ^ d) i ∧
      ↑(deltaSeq d m (i + 1)) = seqDeltaIter m (fun n => (n : ℤ) ^ d) (i + 1) :=
    ⟨deltaSeq_coe d m hm.le i, deltaSeq_coe d m hm.le (i + 1)⟩
  have h_succ : seqDeltaIter m (fun n => (n : ℤ) ^ d) (i + 1) =
      seqDeltaIter m (fun n => (n : ℤ) ^ d) i +
      seqDeltaIter (m + 1) (fun n => (n : ℤ) ^ d) i := by
    simp +decide [seqDeltaIter_succ, seqDelta]
  linarith [seqDeltaIter_nonneg d (m + 1) (by linarith) i]

/-- `deltaSeq d (m+1) i = deltaSeq d m (i+1) - deltaSeq d m i` for `m < d` -/
lemma deltaSeq_succ (d m : ℕ) (hm : m < d) (i : ℕ) :
    deltaSeq d (m + 1) i = deltaSeq d m (i + 1) - deltaSeq d m i := by
  have h_diff : seqDeltaIter (m + 1) (fun n => (n : ℤ) ^ d) i =
      seqDeltaIter m (fun n => (n : ℤ) ^ d) (i + 1) -
      seqDeltaIter m (fun n => (n : ℤ) ^ d) i := by
    erw [seqDeltaIter_succ]; rfl
  have := deltaSeq_coe d (m + 1) (by linarith) i
  have := deltaSeq_coe d m (by linarith) (i + 1)
  have := deltaSeq_coe d m (by linarith) i
  grind +ring

/-- Key decomposition: `deltaSeq d (d-k) i = c · i^k + Σ_{j<k} α_j · i^j`
    where `c = d.descFactorial (d-k)` and `α_j = deltaCoeff d (d-k) j` -/
lemma deltaSeq_decomp (d k : ℕ) (hk : k ≤ d) (i : ℕ) :
    deltaSeq d (d - k) i = d.descFactorial (d - k) * i ^ k +
    ∑ j ∈ range k, deltaCoeff d (d - k) j * i ^ j := by
  rw [← @Nat.cast_inj ℤ]; simp +decide [deltaSeq_coe, seqDeltaIter_eq_sum, *]
  rw [← Finset.sum_range_add_sum_Ico _ (show k ≤ d + 1 from by linarith)]
  rw [add_comm, Finset.sum_Ico_eq_sub _] <;> norm_num [hk]
  · rw [← Finset.sum_erase_add _ _ (Finset.mem_range.mpr (by linarith : k < d + 1)), add_comm]
    rw [← Finset.sum_subset (show Finset.range k ⊆
        (Finset.range (d + 1) |> Finset.erase) k from ?_)] <;>
      norm_num [Finset.subset_iff]
    · exact Or.inl (by simpa [Nat.sub_sub_self hk] using
        deltaCoeff_leading d (d - k) (Nat.sub_le _ _))
    · exact fun x hx₁ hx₂ hx₃ =>
        Or.inl <| deltaCoeff_eq_zero _ _ _ (Nat.sub_le _ _) <| by omega
    · grind
  · linarith

/-! ## Part 4: SeqClosure Axioms -/

/-- Axioms for the sequence closure property.
These abstract the properties of thick tensor ideals used by the proof:
- `add`, `smul`: from Lemma 7.20 (closure under addition and scalar multiplication)
- `sub`: from Lemma C (subtraction / two-out-of-three property)
- `split`: from Lemma B (p-fold splitting, generalized Corollary 7.3)
- `shift`: shift invariance (direct summand + shift from the derived category)
- `const_one`: the constant sequence 1 belongs to T -/
structure SeqClosure (T : (ℕ → ℕ) → Prop) : Prop where
  congr : ∀ {f g}, T f → (∀ i, f i = g i) → T g
  add : ∀ {f g}, T f → T g → T (fun i => f i + g i)
  smul : ∀ (c : ℕ) {f}, T f → T (fun i => c * f i)
  sub : ∀ {f g}, T (fun i => f i + g i) → T g → T f
  split : ∀ (p : ℕ), p ≥ 2 → ∀ {f}, (∀ r, r < p → T (fun i => f (p * i + r))) → T f
  shift : ∀ {f}, T f → T (fun i => f (i + 1))
  const_one : T (fun _ => 1)

/-! ## Part 5: Derived Lemmas from SeqClosure -/

variable {T : (ℕ → ℕ) → Prop}

/-- Forward difference preserves T-membership for non-decreasing sequences.
    Uses: `shift f ∈ T`, and `shift f = fwdDiff f + f`, so `sub` gives `fwdDiff f ∈ T`. -/
lemma mem_fwdDiff (hT : SeqClosure T) {f : ℕ → ℕ} (hf : T f)
    (hmono : ∀ i, f i ≤ f (i + 1)) :
    T (fun i => f (i + 1) - f i) := by
  convert hT.sub ?_ hf using 1
  convert hT.shift hf using 1; aesop

/-- T contains `deltaSeq d m` for all `m ≤ d`, by induction on `m`. -/
lemma mem_deltaSeq (hT : SeqClosure T) {d : ℕ} (m : ℕ) (hm : m ≤ d) (hd : 1 ≤ d)
    (hpow : T (fun i => i ^ d)) :
    T (deltaSeq d m) := by
  induction' m with m ih generalizing d
  · convert hpow using 1
  · have h_diff : T (fun i => deltaSeq d m (i + 1) - deltaSeq d m i) :=
      mem_fwdDiff hT (ih (by linarith) (by linarith) hpow) (deltaSeq_mono d m (by linarith))
    convert h_diff using 1
    exact funext fun i => deltaSeq_succ d m (by linarith) i

/-- A non-negative integer linear combination of sequences in T is in T. -/
lemma mem_lincomb (hT : SeqClosure T) {n : ℕ} (α : Fin n → ℕ) (f : Fin n → ℕ → ℕ)
    (hf : ∀ j, T (f j)) :
    T (fun i => ∑ j : Fin n, α j * f j i) := by
  induction' n with n ih <;> simp +decide [Fin.sum_univ_succ, *]
  · have := hT.smul 0 hT.const_one; aesop
  · exact hT.add (hT.smul _ (hf _)) (ih _ _ fun j => hf _)

/-- If all powers `i^j` for `j < k` are in T, then any non-negative integer linear
    combination `Σ_{j<k} α_j · i^j` is also in T. -/
lemma mem_lower_terms (hT : SeqClosure T) {k : ℕ} (α : Fin k → ℕ)
    (ih : ∀ j : ℕ, j < k → T (fun i => i ^ j)) :
    T (fun i => ∑ j : Fin k, α j * i ^ (j : ℕ)) :=
  mem_lincomb hT α (fun j => (fun i => i ^ (j : ℕ))) (fun j => ih j j.2)

/-- **Splitting step.** If `T (fun i => c · i^k)` with `c ≥ 2` and `T (fun i => i^j)`
    for all `j < k`, then `T (fun i => i^k)`.

    By `split` with `p = c`, it suffices to show `T (fun i => (c·i + r)^k)` for `r < c`.
    The binomial expansion `(c·i + r)^k = c^k · i^k + (lower terms)` has:
    - Leading term `c^k · i^k = c^{k-1} · (c · i^k)` in T by `smul`
    - Lower terms in T by inductive hypothesis and `smul`/`add` -/
lemma splitting_step (hT : SeqClosure T) {k c : ℕ} (hc : 2 ≤ c)
    (h_ci : T (fun i => c * i ^ k))
    (ih : ∀ j : ℕ, j < k → T (fun i => i ^ j)) :
    T (fun i => i ^ k) := by
  suffices h_split : ∀ r < c, T (fun i => (c * i + r) ^ k) from hT.split c hc h_split
  have h_binom : ∀ r < c, (fun i => (c * i + r) ^ k) =
      fun i => ∑ m ∈ Finset.range (k + 1), Nat.choose k m * c ^ m * r ^ (k - m) * i ^ m := by
    intro r hr; ext i; rw [add_pow]; congr; ext; ring; norm_cast
  have h_ind : ∀ r < c, ∀ m ∈ Finset.range (k + 1),
      T (fun i => Nat.choose k m * c ^ m * r ^ (k - m) * i ^ m) := by
    intro r hr m hm
    by_cases hm' : m < k
    · convert hT.smul (Nat.choose k m * c ^ m * r ^ (k - m)) (ih m hm') using 1
    · simp_all +decide [show m = k by linarith [Finset.mem_range.mp hm]]
      induction' k with k _
      · simpa using hT.const_one
      · convert hT.smul (c ^ k) h_ci using 1; ext; ring
  intro r hr; rw [h_binom r hr]
  have h_sum : ∀ {n : ℕ} {f : Fin n → ℕ → ℕ}, (∀ j, T (f j)) →
      T (fun i => ∑ j, f j i) := by
    intros n f hf; induction' n with n ih <;> simp_all +decide [Fin.sum_univ_succ]
    · simpa using hT.smul 0 hT.const_one
    · exact hT.add (hf 0) (ih fun j => hf j.succ)
  simpa only [Finset.sum_range] using h_sum fun j => h_ind r hr j (Finset.mem_range.mpr j.2)

/-! ## Part 6: Main Theorem -/

/-- **Main Theorem (Remark 7.22 for all d ≥ 1).**

If `T` satisfies the `SeqClosure` axioms and contains the sequence `i ↦ i^d`
for some `d ≥ 1`, then `T` contains `i ↦ i^k` for all `0 ≤ k ≤ d`.

This proves that the generalization of Example 7.21 to degree-d polynomials
holds for all d ≥ 1, answering the question posed in Remark 7.22 affirmatively.

**Proof outline.** By strong induction on `k`:
- **k = 0**: The constant sequence 1 is in T (`const_one`).
- **k = d**: Given by hypothesis.
- **1 ≤ k < d**: Apply `Δ^{d-k}` to `i^d` to obtain a degree-k polynomial with
  non-negative coefficients. Subtract the lower-order terms (in T by IH) to get
  `c · i^k` where `c = d!/(d-k)! ≥ 2`. Then use `c`-fold splitting to recover `i^k`. -/
theorem all_powers_in_T (hT : SeqClosure T) {d : ℕ} (hd : d ≥ 1) (hpow : T (fun i => i ^ d)) :
    ∀ k, k ≤ d → T (fun i => i ^ k) := by
  have h_ind : ∀ k ≤ d, (∀ j < k, T (fun i => i ^ j)) → T (fun i => i ^ k) := by
    intro k hk ih
    by_cases hk0 : k = 0 ∨ k = d
    · cases hk0 <;> simp_all +decide [hT.const_one]
    · -- 1 ≤ k < d: the inductive step
      have h_deltaSeq : T (deltaSeq d (d - k)) :=
        mem_deltaSeq hT (d - k) (Nat.sub_le d k) hd hpow
      obtain ⟨c, hc⟩ : ∃ c : ℕ, c ≥ 2 ∧ ∀ i,
          deltaSeq d (d - k) i = c * i ^ k +
          ∑ j ∈ Finset.range k, deltaCoeff d (d - k) j * i ^ j :=
        ⟨d.descFactorial (d - k),
          descFactorial_ge_two d k (by omega) (Nat.pos_of_ne_zero (by omega))
            (Nat.le_sub_one_of_lt (by omega)),
          fun i => deltaSeq_decomp d k hk i⟩
      have h_lower : T (fun i => ∑ j ∈ Finset.range k, deltaCoeff d (d - k) j * i ^ j) := by
        convert mem_lower_terms hT (fun j => deltaCoeff d (d - k) j) (fun j hj => ih j hj) using 1
        exact funext fun i => by rw [Finset.sum_range]
      have h_ci : T (fun i => c * i ^ k) := by
        convert hT.sub _ h_lower using 1
        convert h_deltaSeq using 1; ext i; aesop
      exact splitting_step hT hc.1 h_ci ih
  intros k hk
  induction' k using Nat.strong_induction_on with k ih
  exact h_ind k hk fun j hj => ih j hj <| le_trans hj.le hk

end Remark722
