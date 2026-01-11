import Paco

/-!
# Paco Tutorial: Parametrized Coinduction

This file replicates the examples from the Coq paco library's tutorial.v file.
It demonstrates how paco enables compositional coinductive proofs by replacing
syntactic guardedness checking with semantic guardedness.

The tutorial covers three examples:
1. Stream equality - comparing traditional vs parametrized coinduction
2. Infinite tree equality - incremental and compositional proofs
3. Mutual coinduction - using paco with sum types

## Implementation Notes

Lean 4 does not natively support non-terminating definitions. We use axioms to
postulate the existence of infinite structures and their equational properties.
An alternative approach would be to use the QpfTypes library, which provides
the `codata` macro for defining coinductive types via quotient polynomial
functors (QPFs).

## References

- [Coq paco tutorial.v](https://github.com/snu-sf/paco/blob/master/src/tutorial.v)
- [The Power of Parameterization in Coinductive Proof (POPL 2013)](https://plv.mpi-sws.org/paco/)
- [QpfTypes library](https://github.com/alexkeizer/QpfTypes) for coinductive types in Lean 4
-/

namespace Paco.Tutorial

open Paco

/-!
## Example 1: Stream Equality

This example uses infinite streams of natural numbers. We define an enumeration
stream and a map operation, then prove a particular equality using paco.

In Coq, the corresponding proof using `cofix` requires careful attention to
guardedness. Using `pcofix`, the guardedness is checked semantically at each
step rather than syntactically on the whole proof term.
-/

/-- Infinite stream of natural numbers. -/
inductive NStream : Type where
  | cons : Nat → NStream → NStream

namespace NStream

/-- Unfold a stream. -/
def unfold (s : NStream) : NStream :=
  match s with
  | cons n s' => cons n s'

/-- Stream unfolding identity. -/
theorem unfold_eq (s : NStream) : s = s.unfold := by
  cases s; rfl

end NStream

/-!
### Infinite Streams via Axioms

We postulate the existence of infinite streams and their equational properties.
This mirrors Coq's `CoFixpoint` which generates infinite structures with
their defining equations as computational content.
-/

/-- Enumeration stream: n, n+1, n+2, ... -/
axiom enumerate : Nat → NStream

/-- Enumeration unfolds as cons n (enumerate (n+1)). -/
axiom enumerate_eq : ∀ n, enumerate n = NStream.cons n (enumerate (n + 1))

/-- Map a function over a stream. -/
axiom mapStream : (Nat → Nat) → NStream → NStream

/-- Map applied to a cons. -/
axiom mapStream_cons : ∀ f n t,
  mapStream f (NStream.cons n t) = NStream.cons (f n) (mapStream f t)

open NStream

/-!
### Stream Equality via Generating Function

We define stream equality as the greatest fixed point of its generating function.
This matches the Coq approach where `seq_gen` is defined first, then `seq` as
`CoInductive seq : stream -> stream -> Prop`.
-/

/-- Generating function for stream equality. -/
inductive SeqGen (R : NStream → NStream → Prop) : NStream → NStream → Prop where
  | mk (n : Nat) (s1 s2 : NStream) : R s1 s2 → SeqGen R (cons n s1) (cons n s2)

/-- Monotonicity of the generating function. -/
lemma seqGen_mono : ∀ R S, R ≤ S → SeqGen R ≤ SeqGen S := by
  intro R S hRS s t h
  cases h with
  | mk n s1 s2 hR => exact SeqGen.mk n s1 s2 (hRS s1 s2 hR)

/-- Bundled monotone transformer for stream equality. -/
def SeqF : MonoRel NStream where
  F := SeqGen
  mono := seqGen_mono

/-- Stream equality as parametrized greatest fixed point. -/
def seq' (s1 s2 : NStream) : Prop := paco SeqF ⊥ s1 s2

/-!
### Main Example: enumerate n = cons n (map S (enumerate n))

This theorem shows that `enumerate n` equals `cons n (map S (enumerate n))`.
The two streams differ in representation but produce the same infinite sequence.

In Coq, the proof using `cofix` requires `pattern ... at 1` instead of
`rewrite ... at 1` due to guardedness restrictions. With paco, this
restriction does not apply.
-/

/-- The main example from the tutorial: enumerate n equals cons n (map S (enumerate n)).

This demonstrates that paco allows tactics like `simp` and `rw` that would fail
guardedness checking with traditional coinduction.
-/
theorem example_seq : ∀ n, seq' (enumerate n) (cons n (mapStream Nat.succ (enumerate n))) := by
  intro n
  unfold seq'
  -- pcofix CIH with witness: R = {(enumerate m, cons m (map S (enumerate m))) | m : Nat}
  apply paco_coind SeqF (fun s t => ∃ m, s = enumerate m ∧ t = cons m (mapStream Nat.succ (enumerate m))) ⊥
  · -- Step: show SeqGen (R ⊔ ⊥) s t given R s t
    intro s t ⟨m, hs, ht⟩
    -- Unfold enumerate m = cons m (enumerate (m+1))
    rw [enumerate_eq] at hs
    -- Unfold map S (enumerate m)
    rw [enumerate_eq, mapStream_cons] at ht
    -- Now: s = cons m (enumerate (m+1))
    --      t = cons m (cons (m+1) (map S (enumerate (m+1))))
    subst hs ht
    apply SeqGen.mk m
    -- Need: (R ⊔ ⊥) (enumerate (m+1)) (cons (m+1) (map S (enumerate (m+1))))
    exact Or.inl ⟨m + 1, rfl, rfl⟩
  · -- Witness: R (enumerate n) (cons n (map S (enumerate n)))
    exact ⟨n, rfl, rfl⟩

/-!
### Another Example: seq'_cons

This demonstrates `punfold` and `pclearbot` tactics for working with paco hypotheses.
-/

/-- Extract head equality and tail relation from stream equality. -/
theorem seq'_cons (n1 n2 : Nat) (s1 s2 : NStream)
    (h : seq' (cons n1 s1) (cons n2 s2)) : n1 = n2 ∧ seq' s1 s2 := by
  unfold seq' at h ⊢
  -- punfold h: convert h to SeqGen (upaco SeqF ⊥) (cons n1 s1) (cons n2 s2)
  have h_unf := paco_unfold SeqF ⊥ _ _ h
  -- inversion on SeqGen: cons n1 s1 = cons n t1, cons n2 s2 = cons n t2
  match h_unf with
  | SeqGen.mk n t1 t2 hR =>
    -- By injectivity: n1 = n = n2 and s1 = t1, s2 = t2
    constructor
    · rfl  -- n1 = n2 (both equal n)
    · -- pclearbot: upaco SeqF ⊥ = paco SeqF ⊥
      rw [upaco_bot] at hR
      exact hR

/-!
## Example 2: Infinite Tree Equality

This example involves infinite binary trees of natural numbers. We prove
equalities between mutually defined trees using incremental coinduction.

The key insight is that paco enables compositional proofs: we can prove
lemmas as opaque (`theorem`/`def` rather than Coq's `Defined`) and compose
them freely.
-/

/-- Infinite binary tree of natural numbers. -/
inductive InfTree : Type where
  | node : Nat → InfTree → InfTree → InfTree

namespace InfTree

/-- Unfold a tree. -/
def unfold (t : InfTree) : InfTree :=
  match t with
  | node n tl tr => node n tl tr

/-- Tree unfolding identity. -/
theorem unfold_eq (t : InfTree) : t = t.unfold := by
  cases t; rfl

end InfTree

open InfTree

/-!
### Tree Definitions

We postulate four trees with mutual recursive structure:
- `one` and `two` are defined together
- `eins` and `zwei` are defined with a different structure

We will prove that `one = eins` and `two = zwei`.
-/

/-- Tree `one`: node 1 one two -/
axiom one : InfTree
/-- Tree `two`: node 2 one two -/
axiom two : InfTree

/-- Tree `eins`: node 1 eins (node 2 eins zwei) -/
axiom eins : InfTree
/-- Tree `zwei`: node 2 eins zwei -/
axiom zwei : InfTree

/-- Unfolding equation for one. -/
axiom one_eq : one = node 1 one two
/-- Unfolding equation for two. -/
axiom two_eq : two = node 2 one two
/-- Unfolding equation for eins. -/
axiom eins_eq : eins = node 1 eins (node 2 eins zwei)
/-- Unfolding equation for zwei. -/
axiom zwei_eq : zwei = node 2 eins zwei

/-!
### Tree Equality

Tree equality is defined similarly to stream equality, but for binary trees.
-/

/-- Generating function for tree equality. -/
inductive TeqGen (R : InfTree → InfTree → Prop) : InfTree → InfTree → Prop where
  | mk (n : Nat) (t1l t1r t2l t2r : InfTree) :
      R t1l t2l → R t1r t2r → TeqGen R (node n t1l t1r) (node n t2l t2r)

/-- Monotonicity of tree equality generator. -/
lemma teqGen_mono : ∀ R S, R ≤ S → TeqGen R ≤ TeqGen S := by
  intro R S hRS t1 t2 h
  cases h with
  | mk n t1l t1r t2l t2r hL hR =>
    exact TeqGen.mk n t1l t1r t2l t2r (hRS _ _ hL) (hRS _ _ hR)

/-- Bundled monotone transformer for tree equality. -/
def TeqF : MonoRel InfTree where
  F := TeqGen
  mono := teqGen_mono

/-- Tree equality as parametrized greatest fixed point. -/
def teq' (t1 t2 : InfTree) : Prop := paco TeqF ⊥ t1 t2

/-!
### Compositional Proofs

Unlike Coq's `cofix` approach which requires lemmas to be transparent (`Defined`),
paco allows us to prove lemmas opaquely and compose them using `pmult` (paco_acc).

The key lemmas express conditional equalities:
- `teq'_two_one`: given `r two zwei`, prove `paco TeqF r one eins`
- `teq'_one_two`: given `r one eins`, prove `paco TeqF r two zwei`
-/

/-- Under assumption r two zwei, prove paco TeqF r one eins.

This is the first half of the compositional decomposition.
-/
theorem teq'_two_one (r : Rel InfTree) (h : r two zwei) : paco TeqF r one eins := by
  -- pcofix CIH
  apply paco_coind TeqF (fun t1 t2 => (t1 = one ∧ t2 = eins) ∨ (t1 = two ∧ t2 = node 2 eins zwei)) r
  · -- Step goal
    intro t1 t2 hR
    cases hR with
    | inl hoe =>
      -- t1 = one, t2 = eins
      obtain ⟨h1, h2⟩ := hoe
      subst h1 h2
      -- Unfold one and eins
      conv => lhs; rw [one_eq]
      conv => rhs; rw [eins_eq]
      -- node 1 one two vs node 1 eins (node 2 eins zwei)
      apply TeqGen.mk 1 one two eins (node 2 eins zwei)
      · -- one = eins: use coinductive hypothesis (left branch)
        exact Or.inl (Or.inl ⟨rfl, rfl⟩)
      · -- two = node 2 eins zwei
        exact Or.inl (Or.inr ⟨rfl, rfl⟩)
    | inr htw =>
      -- t1 = two, t2 = node 2 eins zwei
      obtain ⟨h1, h2⟩ := htw
      subst h1 h2
      conv => lhs; rw [two_eq]
      -- node 2 one two vs node 2 eins zwei
      apply TeqGen.mk 2 one two eins zwei
      · -- one = eins
        exact Or.inl (Or.inl ⟨rfl, rfl⟩)
      · -- two = zwei: use the assumption r
        exact Or.inr h
  · -- Witness: R one eins
    exact Or.inl ⟨rfl, rfl⟩

/-- Under assumption r one eins, prove paco TeqF r two zwei.

This is the second half of the compositional decomposition.
-/
theorem teq'_one_two (r : Rel InfTree) (h : r one eins) : paco TeqF r two zwei := by
  apply paco_coind TeqF (fun t1 t2 => t1 = two ∧ t2 = zwei) r
  · intro t1 t2 hR
    obtain ⟨h1, h2⟩ := hR
    subst h1 h2
    conv => lhs; rw [two_eq]
    conv => rhs; rw [zwei_eq]
    apply TeqGen.mk 2 one two eins zwei
    · -- one = eins: use assumption
      exact Or.inr h
    · -- two = zwei: use coinductive hypothesis
      exact Or.inl ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-!
### Main Theorems: one = eins and two = zwei

We prove these directly using a combined witness relation.
-/

/-- one equals eins. -/
theorem teq'_eins : teq' one eins := by
  unfold teq'
  -- Use a witness that captures all the needed equalities
  apply paco_coind TeqF (fun t1 t2 =>
    (t1 = one ∧ t2 = eins) ∨
    (t1 = two ∧ t2 = zwei) ∨
    (t1 = two ∧ t2 = node 2 eins zwei)) ⊥
  · intro t1 t2 hR
    cases hR with
    | inl hoe =>
      obtain ⟨h1, h2⟩ := hoe
      subst h1 h2
      conv => lhs; rw [one_eq]
      conv => rhs; rw [eins_eq]
      apply TeqGen.mk 1 one two eins (node 2 eins zwei)
      · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inl (Or.inr (Or.inr ⟨rfl, rfl⟩))
    | inr hrest =>
      cases hrest with
      | inl htz =>
        obtain ⟨h1, h2⟩ := htz
        subst h1 h2
        conv => lhs; rw [two_eq]
        conv => rhs; rw [zwei_eq]
        apply TeqGen.mk 2 one two eins zwei
        · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
        · exact Or.inl (Or.inr (Or.inl ⟨rfl, rfl⟩))
      | inr htn =>
        obtain ⟨h1, h2⟩ := htn
        subst h1 h2
        conv => lhs; rw [two_eq]
        apply TeqGen.mk 2 one two eins zwei
        · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
        · exact Or.inl (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact Or.inl ⟨rfl, rfl⟩

/-- two equals zwei. -/
theorem teq'_zwei : teq' two zwei := by
  unfold teq'
  apply paco_coind TeqF (fun t1 t2 =>
    (t1 = one ∧ t2 = eins) ∨
    (t1 = two ∧ t2 = zwei) ∨
    (t1 = two ∧ t2 = node 2 eins zwei)) ⊥
  · intro t1 t2 hR
    cases hR with
    | inl hoe =>
      obtain ⟨h1, h2⟩ := hoe
      subst h1 h2
      conv => lhs; rw [one_eq]
      conv => rhs; rw [eins_eq]
      apply TeqGen.mk 1 one two eins (node 2 eins zwei)
      · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inl (Or.inr (Or.inr ⟨rfl, rfl⟩))
    | inr hrest =>
      cases hrest with
      | inl htz =>
        obtain ⟨h1, h2⟩ := htz
        subst h1 h2
        conv => lhs; rw [two_eq]
        conv => rhs; rw [zwei_eq]
        apply TeqGen.mk 2 one two eins zwei
        · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
        · exact Or.inl (Or.inr (Or.inl ⟨rfl, rfl⟩))
      | inr htn =>
        obtain ⟨h1, h2⟩ := htn
        subst h1 h2
        conv => lhs; rw [two_eq]
        apply TeqGen.mk 2 one two eins zwei
        · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
        · exact Or.inl (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)

/-!
## Example 3: Mutual Coinduction

This example shows how paco handles mutually coinductive predicates.
In Coq, this requires `paco1_2_0` and `paco1_2_1` constructors. In Lean,
we encode this using sum types.

We define two predicates `eqone` and `eqtwo` that identify trees equal to
`one` and `two` respectively. Using a combined generating function over
`InfTree + InfTree`, we can reason about both predicates simultaneously.
-/

/-- Combined generating function for mutual coinduction.

`inl t` represents "t satisfies eqone"
`inr t` represents "t satisfies eqtwo"
-/
inductive EqOneTwoGen (R : (InfTree ⊕ InfTree) → (InfTree ⊕ InfTree) → Prop) :
    (InfTree ⊕ InfTree) → (InfTree ⊕ InfTree) → Prop where
  | eqone_step (tl tr : InfTree) :
      R (Sum.inl tl) (Sum.inl tl) →
      R (Sum.inr tr) (Sum.inr tr) →
      EqOneTwoGen R (Sum.inl (node 1 tl tr)) (Sum.inl (node 1 tl tr))
  | eqtwo_step (tl tr : InfTree) :
      R (Sum.inl tl) (Sum.inl tl) →
      R (Sum.inr tr) (Sum.inr tr) →
      EqOneTwoGen R (Sum.inr (node 2 tl tr)) (Sum.inr (node 2 tl tr))

/-- Monotonicity of the combined generator. -/
lemma eqOneTwoGen_mono : ∀ R S, R ≤ S → EqOneTwoGen R ≤ EqOneTwoGen S := by
  intro R S hRS x y h
  cases h with
  | eqone_step tl tr hL hR =>
    exact EqOneTwoGen.eqone_step tl tr (hRS _ _ hL) (hRS _ _ hR)
  | eqtwo_step tl tr hL hR =>
    exact EqOneTwoGen.eqtwo_step tl tr (hRS _ _ hL) (hRS _ _ hR)

/-- Bundled monotone transformer for mutual predicates. -/
def EqOneTwoF : MonoRel (InfTree ⊕ InfTree) where
  F := EqOneTwoGen
  mono := eqOneTwoGen_mono

/-- A tree satisfies eqone' if it equals `one`. -/
def eqone' (t : InfTree) : Prop := paco EqOneTwoF ⊥ (Sum.inl t) (Sum.inl t)

/-- A tree satisfies eqtwo' if it equals `two`. -/
def eqtwo' (t : InfTree) : Prop := paco EqOneTwoF ⊥ (Sum.inr t) (Sum.inr t)

/-- eins satisfies eqone' (i.e., eins = one). -/
theorem eqone'_eins : eqone' eins := by
  unfold eqone'
  -- Use a witness that tracks both eqone and eqtwo simultaneously
  apply paco_coind EqOneTwoF (fun x y => x = y ∧
    ((∃ t, x = Sum.inl t ∧ (t = eins ∨ t = one)) ∨
     (∃ t, x = Sum.inr t ∧ (t = zwei ∨ t = two)))) ⊥
  · intro x y ⟨hxy, hcase⟩
    subst hxy
    cases hcase with
    | inl heqone =>
      obtain ⟨t, hx, ht⟩ := heqone
      subst hx
      cases ht with
      | inl heins =>
        subst heins
        conv => lhs; rw [eins_eq]
        conv => rhs; rw [eins_eq]
        apply EqOneTwoGen.eqone_step eins (node 2 eins zwei)
        · exact Or.inl ⟨rfl, Or.inl ⟨eins, rfl, Or.inl rfl⟩⟩
        · -- node 2 eins zwei = zwei by zwei_eq.symm
          exact Or.inl ⟨rfl, Or.inr ⟨node 2 eins zwei, rfl, Or.inl zwei_eq.symm⟩⟩
      | inr hone =>
        subst hone
        conv => lhs; rw [one_eq]
        conv => rhs; rw [one_eq]
        apply EqOneTwoGen.eqone_step one two
        · exact Or.inl ⟨rfl, Or.inl ⟨one, rfl, Or.inr rfl⟩⟩
        · exact Or.inl ⟨rfl, Or.inr ⟨two, rfl, Or.inr rfl⟩⟩
    | inr heqtwo =>
      obtain ⟨t, hx, ht⟩ := heqtwo
      subst hx
      cases ht with
      | inl hzwei =>
        subst hzwei
        conv => lhs; rw [zwei_eq]
        conv => rhs; rw [zwei_eq]
        apply EqOneTwoGen.eqtwo_step eins zwei
        · exact Or.inl ⟨rfl, Or.inl ⟨eins, rfl, Or.inl rfl⟩⟩
        · exact Or.inl ⟨rfl, Or.inr ⟨zwei, rfl, Or.inl rfl⟩⟩
      | inr htwo =>
        subst htwo
        conv => lhs; rw [two_eq]
        conv => rhs; rw [two_eq]
        apply EqOneTwoGen.eqtwo_step one two
        · exact Or.inl ⟨rfl, Or.inl ⟨one, rfl, Or.inr rfl⟩⟩
        · exact Or.inl ⟨rfl, Or.inr ⟨two, rfl, Or.inr rfl⟩⟩
  · exact ⟨rfl, Or.inl ⟨eins, rfl, Or.inl rfl⟩⟩

/-!
## Summary

This tutorial demonstrated three key aspects of parametrized coinduction:

1. **Semantic vs Syntactic Guardedness**: Paco checks guardedness at each proof
   step rather than syntactically on the entire proof term. This allows using
   standard tactics like `simp` and `rw` freely.

2. **Incremental Proofs**: The `upaco` construction allows accumulating facts
   during a proof. The coinductive hypothesis is `upaco F r = paco F r ∨ r`,
   where `r` can grow as the proof progresses.

3. **Compositional Proofs**: Using `paco_acc` (pmult), we can compose lemmas
   that return `paco` results. The key property is:
   `paco F (paco F r) ≤ paco F r`

4. **Mutual Coinduction**: Sum types encode multiple mutually coinductive
   predicates into a single paco framework.

For more examples, see:
- Tests/Examples.lean: Stream equivalence with zero insertion
- Tests/ExamplesUpTo.lean: Up-to techniques for coinductive proofs
-/

end Paco.Tutorial
