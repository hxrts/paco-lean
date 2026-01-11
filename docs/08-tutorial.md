# Tutorial: Parametrized Coinduction Examples

This tutorial walks through three examples that demonstrate parametrized coinduction. The examples are based on the Coq paco library tutorial. Each example shows how paco simplifies coinductive proofs compared to traditional approaches.

The corresponding Lean code is in `Tests/Tutorial.lean`. The three examples cover stream equality, infinite tree equality, and mutual coinduction.

## Prerequisites

This tutorial assumes familiarity with the concepts in [Basic Usage Tutorial](04-basic-usage.md). Understanding the `paco`, `upaco`, and `paco_coind` definitions is essential.

## Example 1: Stream Equality

This example defines infinite streams of natural numbers. It proves that two differently-constructed streams are equal.

### Stream Definition

Streams are defined as an inductive type with a single constructor.

```lean
inductive NStream : Type where
  | cons : Nat → NStream → NStream
```

This definition captures the structure of a stream. Each stream consists of a head value and a tail stream. The type is finite, but we will postulate infinite inhabitants.

### Infinite Streams via Axioms

Lean 4 does not support non-terminating definitions directly. We use axioms to postulate infinite streams and their equational properties.

```lean
axiom enumerate : Nat → NStream
axiom enumerate_eq : ∀ n, enumerate n = NStream.cons n (enumerate (n + 1))
axiom mapStream : (Nat → Nat) → NStream → NStream
axiom mapStream_cons : ∀ f n t,
  mapStream f (NStream.cons n t) = NStream.cons (f n) (mapStream f t)
```

The `enumerate n` stream contains the values n, n+1, n+2, and so on. The `mapStream` function applies a function to each element. These axioms give us the computational equations without requiring termination proofs.

An alternative approach is to use the QpfTypes library. That library provides the `codata` macro for defining coinductive types via quotient polynomial functors.

### Stream Equality Generator

Stream equality is defined as the greatest fixed point of a generating function.

```lean
inductive SeqGen (R : NStream → NStream → Prop) : NStream → NStream → Prop where
  | mk (n : Nat) (s1 s2 : NStream) : R s1 s2 → SeqGen R (cons n s1) (cons n s2)

def SeqF : MonoRel NStream where
  F := SeqGen
  mono := seqGen_mono

def seq' (s1 s2 : NStream) : Prop := paco SeqF ⊥ s1 s2
```

The generator `SeqGen` relates two streams when they have the same head and their tails are related by R. The `SeqF` bundled transformer satisfies monotonicity automatically. The `seq'` predicate instantiates paco with an empty accumulator.

### Main Example

The main theorem proves that `enumerate n` equals `cons n (mapStream Nat.succ (enumerate n))`.

```lean
theorem example_seq : ∀ n, seq' (enumerate n) (cons n (mapStream Nat.succ (enumerate n))) := by
  intro n
  unfold seq'
  apply paco_coind SeqF (fun s t => ∃ m, s = enumerate m ∧ t = cons m (mapStream Nat.succ (enumerate m))) ⊥
  · intro s t ⟨m, hs, ht⟩
    rw [enumerate_eq] at hs
    rw [enumerate_eq, mapStream_cons] at ht
    subst hs ht
    apply SeqGen.mk m
    exact Or.inl ⟨m + 1, rfl, rfl⟩
  · exact ⟨n, rfl, rfl⟩
```

The proof uses `paco_coind` with a witness relation. The witness captures all pairs of the form `(enumerate m, cons m (mapStream Nat.succ (enumerate m)))`. After unfolding the definitions, the generator step follows directly.

In Coq, this proof using `cofix` requires `pattern ... at 1` instead of `rewrite ... at 1`. The syntactic guardedness checker rejects the rewrite. With paco, guardedness is checked semantically at each step. This allows standard tactics like `simp` and `rw` to work freely.

### Extracting Stream Components

The `seq'_cons` theorem shows how to extract information from stream equality.

```lean
theorem seq'_cons (n1 n2 : Nat) (s1 s2 : NStream)
    (h : seq' (cons n1 s1) (cons n2 s2)) : n1 = n2 ∧ seq' s1 s2 := by
  unfold seq' at h ⊢
  have h_unf := paco_unfold SeqF ⊥ _ _ h
  match h_unf with
  | SeqGen.mk n t1 t2 hR =>
    constructor
    · rfl
    · rw [upaco_bot] at hR
      exact hR
```

The proof unfolds the paco definition using `paco_unfold`. Pattern matching on the generator reveals that both streams have the same head. The tail relation follows from `upaco_bot`, which simplifies `upaco F ⊥` to `paco F ⊥`.

## Example 2: Infinite Tree Equality

This example involves infinite binary trees. It demonstrates compositional proofs using paco.

### Tree Definition

Trees are defined with a single constructor taking a value and two subtrees.

```lean
inductive InfTree : Type where
  | node : Nat → InfTree → InfTree → InfTree
```

The structure is similar to streams but with two children instead of one. We again use axioms for infinite inhabitants.

### Mutually Recursive Trees

We postulate four trees with mutual recursive structure.

```lean
axiom one : InfTree
axiom two : InfTree
axiom eins : InfTree
axiom zwei : InfTree

axiom one_eq : one = node 1 one two
axiom two_eq : two = node 2 one two
axiom eins_eq : eins = node 1 eins (node 2 eins zwei)
axiom zwei_eq : zwei = node 2 eins zwei
```

The trees `one` and `two` are defined mutually. The trees `eins` and `zwei` have a different structure but represent the same infinite objects. The goal is to prove `one = eins` and `two = zwei`.

### Tree Equality Generator

Tree equality follows the same pattern as stream equality.

```lean
inductive TeqGen (R : InfTree → InfTree → Prop) : InfTree → InfTree → Prop where
  | mk (n : Nat) (t1l t1r t2l t2r : InfTree) :
      R t1l t2l → R t1r t2r → TeqGen R (node n t1l t1r) (node n t2l t2r)

def TeqF : MonoRel InfTree where
  F := TeqGen
  mono := teqGen_mono

def teq' (t1 t2 : InfTree) : Prop := paco TeqF ⊥ t1 t2
```

The generator requires the same root value and related subtrees. This captures the coinductive nature of tree equality.

### Compositional Proof Strategy

Unlike Coq's `cofix` approach, paco allows opaque lemmas. We can prove conditional equalities as separate theorems and compose them.

```lean
theorem teq'_two_one (r : Rel InfTree) (h : r two zwei) : paco TeqF r one eins := by
  apply paco_coind TeqF (fun t1 t2 => (t1 = one ∧ t2 = eins) ∨ (t1 = two ∧ t2 = node 2 eins zwei)) r
  · intro t1 t2 hR
    cases hR with
    | inl hoe =>
      obtain ⟨h1, h2⟩ := hoe
      subst h1 h2
      conv => lhs; rw [one_eq]
      conv => rhs; rw [eins_eq]
      apply TeqGen.mk 1 one two eins (node 2 eins zwei)
      · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inl (Or.inr ⟨rfl, rfl⟩)
    | inr htw =>
      obtain ⟨h1, h2⟩ := htw
      subst h1 h2
      conv => lhs; rw [two_eq]
      apply TeqGen.mk 2 one two eins zwei
      · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr h
  · exact Or.inl ⟨rfl, rfl⟩
```

The `teq'_two_one` theorem proves `paco TeqF r one eins` under the assumption `r two zwei`. It parametrizes over an arbitrary relation r. When we need the fact that `two = zwei`, we use the assumption r.

A similar theorem `teq'_one_two` proves the converse direction. These lemmas can be composed using `paco_acc` to prove the final result.

### Main Theorems

The final theorems prove `one = eins` and `two = zwei` directly.

```lean
theorem teq'_eins : teq' one eins := by
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
      -- handle remaining cases...
  · exact Or.inl ⟨rfl, rfl⟩
```

The witness relation captures all needed pairs simultaneously. This avoids the need to compose separate lemmas. The proof handles each case by unfolding the tree definitions and applying the generator.

## Example 3: Mutual Coinduction

This example shows how paco handles mutually coinductive predicates. In Coq, this requires specialized `paco1_2_0` and `paco1_2_1` constructors. In Lean, we use sum types.

### Encoding Mutual Predicates

We define two predicates `eqone` and `eqtwo` that identify trees equal to `one` and `two` respectively.

```lean
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
```

The type `InfTree ⊕ InfTree` tags which predicate applies. Elements of the form `Sum.inl t` represent "t satisfies eqone". Elements of the form `Sum.inr t` represent "t satisfies eqtwo".

The generator has two constructors. The `eqone_step` constructor handles trees with root 1. The `eqtwo_step` constructor handles trees with root 2. Each requires the subtrees to satisfy the appropriate predicates.

### Mutual Predicate Definitions

The individual predicates are projections from the combined paco.

```lean
def EqOneTwoF : MonoRel (InfTree ⊕ InfTree) where
  F := EqOneTwoGen
  mono := eqOneTwoGen_mono

def eqone' (t : InfTree) : Prop := paco EqOneTwoF ⊥ (Sum.inl t) (Sum.inl t)
def eqtwo' (t : InfTree) : Prop := paco EqOneTwoF ⊥ (Sum.inr t) (Sum.inr t)
```

The `EqOneTwoF` bundled transformer handles both predicates. The `eqone'` predicate specializes to the left injection. The `eqtwo'` predicate specializes to the right injection.

### Mutual Coinduction Proof

The theorem `eqone'_eins` proves that `eins` satisfies `eqone'`.

```lean
theorem eqone'_eins : eqone' eins := by
  unfold eqone'
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
        · exact Or.inl ⟨rfl, Or.inr ⟨node 2 eins zwei, rfl, Or.inl zwei_eq.symm⟩⟩
      | inr hone =>
        -- handle one case...
    | inr heqtwo =>
      -- handle eqtwo cases...
  · exact ⟨rfl, Or.inl ⟨eins, rfl, Or.inl rfl⟩⟩
```

The witness relation tracks both `eqone` and `eqtwo` simultaneously. Each case unfolds the tree definition and applies the appropriate generator constructor. The mutual structure is captured in the sum type encoding.

## Key Takeaways

Parametrized coinduction provides semantic guardedness checking. Traditional `cofix` checks guardedness syntactically on the entire proof term. Paco checks guardedness at each step independently. This allows standard tactics to work without restriction.

The `upaco` construction enables incremental proofs. The coinductive hypothesis is `upaco F r = paco F r ∨ r`. The parameter r can accumulate facts as the proof progresses. This is essential for compositional reasoning.

The `paco_acc` theorem enables composition. The key property is `paco F (paco F r) ≤ paco F r`. Lemmas that return paco results can be composed without exposing their internal structure. This matches the opacity benefits of Coq's `theorem` over `Defined`.

Sum types encode mutual coinduction. Multiple mutually coinductive predicates become a single paco over a sum type. The encoding is straightforward and requires no specialized library support.

## Further Reading

See [Tests/Examples.lean](../Tests/Examples.lean) for stream equivalence with zero insertion. See [Tests/ExamplesUpTo.lean](../Tests/ExamplesUpTo.lean) for up-to techniques in coinductive proofs. The [Up-To Techniques Guide](06-upto-guide.md) covers closure operators and compatibility.
