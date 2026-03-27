This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# Formalization Status

This project contains a Lean 4 formalization of the core argument behind Remark 7.22, in
`RequestProject/Remark722.lean`.

The file builds successfully and does not use `sorry` or `admit`. In that sense, it is a
genuine machine-checked proof.

However, the formalization is not yet the full end-to-end formalization of the original
mathematical setting. It proves an abstract theorem about predicates on sequences
`T : (ℕ → ℕ) → Prop`, under a package of axioms called `SeqClosure`, rather than formalizing
the full derived-category / thick-tensor-ideal context directly.

# What Is Already Formalized

The current development fully formalizes the combinatorial and inductive core of the proof:

- forward finite differences of power sequences;
- coefficient analysis for iterated differences of `i^d`;
- nonnegativity and degree control for those iterated differences;
- the abstract closure argument showing that if `T` contains `i ↦ i^d`, then `T` contains
  every `i ↦ i^k` for `k ≤ d`, provided `T` satisfies `SeqClosure`.

In short, the theorem currently proved is:

> If `T` satisfies the `SeqClosure` axioms and `T` contains `i ↦ i^d` for some `d ≥ 1`,
> then `T` also contains `i ↦ i^k` for every `k ≤ d`.

This means the proof assistant has checked the core algebraic mechanism of the argument, not
just a sketch of it.

# Gap From the Original Proof

The main gap is not inside the finite-difference argument. The gap is the bridge from the
original mathematical objects to the abstract `SeqClosure` framework.

The current file replaces the original background theory with axioms:

- `add`, `smul`, `sub`;
- `split`;
- `shift`;
- `const_one`;
- extensionality via `congr`.

This is mathematically reasonable and isolates the exact properties used by the proof, but it
means the current theorem is a relative formalization:

- it formalizes the implication from the closure properties to the conclusion;
- it does not yet formalize the concrete category-theoretic world in which those closure
  properties are supposed to hold.

So the present result is best described as:

> The core proof is formalized, but the semantic interpretation of the abstract predicate `T`
> as the specific object from the original paper has not yet been formalized.

# Gap From the Original Problem

If the original question is interpreted as:

> "Is the induction / finite-difference / splitting argument correct in full generality?"

then this repository is already very close to a complete answer.

If the original question is interpreted as:

> "Has the original statement, in its native derived-category or thick-tensor-ideal setting,
> been fully formalized in Lean?"

then there is still a real gap.

That gap is the missing formalized bridge:

1. define the concrete mathematical objects from the original source;
2. define the concrete predicate `T` coming from that setting;
3. prove that this concrete `T` satisfies `SeqClosure`;
4. instantiate `all_powers_in_T` with that concrete `T`;
5. derive the original theorem as a corollary in its native language.

# What Would Be Needed for a Full End-to-End Formalization

To reduce the gap to the original statement, the next steps would likely be:

1. Formalize the ambient category-theoretic setting used in the paper.
2. Formalize the relevant notion of thick tensor ideal or the exact substitute used by the
   original argument.
3. Define the sequence-valued predicate corresponding to membership in that ideal.
4. Prove each `SeqClosure` field from the actual theory:
   `congr`, `add`, `smul`, `sub`, `split`, `shift`, and `const_one`.
5. State the original theorem in its native objects and show it reduces to
   `all_powers_in_T`.
6. Add a final theorem whose statement matches the original remark as closely as possible,
   with no remaining abstract interface in the user-facing theorem.

# Practical Assessment

A fair assessment of the current repository is:

- stronger than an informal proof sketch;
- stronger than a partially formalized argument;
- weaker than a full formalization of the original paper context.

The mathematically hardest proof pattern appears to be checked already. The remaining work is
mostly semantic integration: formalizing the ambient theory and proving that the abstract
axioms used here are actually satisfied by the original objects of interest.
