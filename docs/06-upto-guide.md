# Up-To Techniques Guide

This guide covers advanced up-to reasoning with closure operators. Up-to techniques enhance coinductive proofs by allowing reasoning modulo some closure.

## What Are Up-To Techniques

Standard coinduction requires proving `R ⊆ F(R)` for a witness relation R. Up-to techniques relax this to `R ⊆ F(clo(R))` for some closure operator `clo`. The closure expands R before checking the post-fixpoint condition.

This relaxation is sound when the closure is compatible with F. Compatible closures preserve the structure that F requires. The key insight is that `clo(gfp F) ⊆ gfp F` when `clo` is compatible.

## Closure Operators

A closure operator expands a relation while preserving certain properties. The library provides several standard closures.

### Reflexive Closure

The reflexive closure adds identity pairs.

```lean
def reflClosure (R : Rel α) : Rel α := fun x y => x = y ∨ R x y
```

This closure is useful when you want to reason "up to equality". Elements can be related through R or by being equal.

### Symmetric Closure

The symmetric closure adds reverse pairs.

```lean
def symmClosure (R : Rel α) : Rel α := fun x y => R x y ∨ R y x
```

This closure is useful when the relation you want to prove is symmetric. You only need to establish one direction.

### Transitive Closure

The transitive closure allows chains through intermediate elements.

```lean
inductive transClosure (R : Rel α) : Rel α where
  | base (h : R x y) : transClosure R x y
  | trans (h₁ : transClosure R x z) (h₂ : transClosure R z y) : transClosure R x y
```

This closure is useful for transitivity proofs. You can compose multiple R-steps.

### Reflexive-Transitive Closure

The reflexive-transitive closure combines reflexivity and transitivity.

```lean
inductive rtClosure (R : Rel α) : Rel α where
  | refl : rtClosure R x x
  | base (h : R x y) : rtClosure R x y
  | trans (h₁ : rtClosure R x z) (h₂ : rtClosure R z y) : rtClosure R x y
```

This closure is commonly used for reachability arguments.

### Equivalence Closure

The equivalence closure generates an equivalence relation.

```lean
inductive eqvClosure (R : Rel α) : Rel α where
  | refl : eqvClosure R x x
  | base (h : R x y) : eqvClosure R x y
  | symm (h : eqvClosure R x y) : eqvClosure R y x
  | trans (h₁ : eqvClosure R x z) (h₂ : eqvClosure R z y) : eqvClosure R x y
```

This closure is useful when proving equivalence relations.

## Compatibility

A closure is compatible with F when applying the closure before or after F yields the same containment.

```lean
def Compatible (F : MonoRel α) (clo : Rel α → Rel α) : Prop :=
  ∀ R, clo (F R) ≤ F (clo R)
```

The condition `clo (F R) ≤ F (clo R)` ensures that closure-expanded F-steps can be justified by F-steps over closure-expanded relations.

### Conditional Compatibility

Most closures are compatible only with specific classes of F. The library provides conditional compatibility theorems.

```lean
theorem reflClosure_compatible (F : MonoRel α)
    (hF_refl : ∀ R : Rel α, (∀ x, R x x) → ∀ x, F R x x) :
    Compatible F reflClosure
```

Reflexive closure is compatible when F preserves reflexivity. If R is reflexive and F respects that, then reflClosure works as an up-to technique.

```lean
theorem symmClosure_compatible (F : MonoRel α)
    (hF_symm : ∀ R x y, F R x y → F (symmClosure R) y x) :
    Compatible F symmClosure
```

Symmetric closure is compatible when F respects symmetry.


## Respectfulness

Respectfulness is a weaker condition than compatibility. It is often easier to prove because it makes fewer demands on the closure operator.

The library provides three variants. See the Respectfulness Variants section below for details on when to use each one.

### PRespectful and tagged roundtrip

Lean does not derive `Compatible'` from `PRespectful` without extra assumptions.
The library uses a tagged roundtrip strategy to recover guardedness information.

The roundtrip assumption is `TagRoundtrip F clo`.
It states that closing on `R ⊔ S` is contained in closing on tagged `R` and `S` and then forgetting the tags.

The second assumption is `PrespectRightGuarded F clo`.
It states that the guarded branch of `prespectClosure` is preserved by `F`.

Under these assumptions, `prespect_compatible'_tagged` yields `Compatible'`.
If `F` is inflationary and `clo` is `PRespectfulStrong`, the right-guardedness condition follows automatically.

## The rclo Construction

The `rclo` type accumulates closure applications. It is the smallest relation containing R and closed under a closure operator.

```lean
inductive rclo (clo : Rel α → Rel α) (R : Rel α) : Rel α where
  | base (h : R x y) : rclo clo R x y
  | clo (R' : Rel α) (hR' : R' ≤ rclo clo R) (h : clo R' x y) : rclo clo R x y
```

The `base` constructor injects R into rclo. The `clo` constructor applies the closure to any relation R' contained in rclo. This formulation is more general than direct application to rclo itself.

## GPaco with Closures

The `gpaco_clo` definition integrates closures with gpaco.

```lean
def gpaco_clo (F : MonoRel α) (clo : Rel α → Rel α) (r rg : Rel α) : Rel α :=
  rclo clo (paco (composeRclo F clo) (rg ⊔ r) ⊔ r)
```

The generating function becomes `F ∘ rclo clo`. This composes F with the closure accumulator. The result is wrapped in `rclo clo` to allow closure at the top level.

### Using gpaco_clo

The `gpaco_clo_cofix` theorem provides coinduction for gpaco_clo.

```lean
theorem gpaco_clo_cofix (F : MonoRel α) (clo : Rel α → Rel α)
    (r rg : Rel α) (R : Rel α)
    (step : R ≤ F (rclo clo (R ⊔ upaco (composeRclo F clo) (rg ⊔ r))) ⊔ r)
    {x y : α} (hxy : R x y) : gpaco_clo F clo r rg x y
```

The step function receives `rclo clo (R ⊔ upaco (composeRclo F clo) (rg ⊔ r))` for recursive calls. This allows applying the closure during recursion.

## The Companion

The companion is the greatest compatible monotone closure. It subsumes all other compatible closures for a given F.

```lean
def companion (F : MonoRel α) : Rel α → Rel α :=
  ⨆ clo, (· : { clo // CloMono clo ∧ Compatible F clo}).val
```

The companion is defined as the supremum over all monotone compatible closures.

### Companion Properties

The companion satisfies several key properties.

```lean
theorem companion_extensive (F : MonoRel α) (R : Rel α) :
    R ≤ companion F R

theorem companion_compat (F : MonoRel α) :
    Compatible F (companion F)

theorem companion_mono (F : MonoRel α) :
    CloMono (companion F)
```

These lemmas state that the companion is extensive, compatible with `F`, and monotone.

### Companion Composition

The companion is also closed under relational composition when `F` is
composition-compatible. The ergonomic workflow is:
1) prove `F` preserves transitive closure
2) derive `CompCompatible F`
3) use `companion_compose` without extra arguments

```lean
/-- If F preserves transitive closure, then transClosure is compatible. --/
theorem transClosure_compatible_of_preserve (F : MonoRel α)
    (h : ∀ R, transClosure (F R) ≤ F (transClosure R)) :
    Compatible F transClosure

/-- F is compatible with relational composition. --/
class CompCompatible (F : MonoRel α) : Prop :=
  (comp : Compatible F transClosure)

-- companion closed under composition
theorem companion_compose (F : MonoRel α) (R : Rel α) [CompCompatible F] :
    ∀ a b c, companion F R a b → companion F R b c → companion F R a c
```

This pattern makes the composition lemma usable without passing a proof argument at each call site.

### Using the Companion

The `companion_coind` wrapper provides coinduction with the companion closure.

```lean
theorem companion_coind {F : MonoRel α} {r rg : Rel α} {x y : α}
    (R : Rel α)
    (witness : R x y)
    (step : R ≤ F (rclo (companion F) (R ⊔ upaco (composeRclo F (companion F)) (rg ⊔ r))) ⊔ r) :
    gpaco_clo F (companion F) r rg x y
```

Using the companion gives you the maximum up-to reasoning power available.

## Composing Closures

Compatible closures can be composed. The `Paco.UpTo.Compose` module provides composition theorems.

```lean
theorem compatible_compose (F : MonoRel α)
    (h₁_mono : CloMono clo₁) (h₁ : Compatible F clo₁) (h₂ : Compatible F clo₂) :
    Compatible F (clo₁ ∘ clo₂)
```

Composing compatible closures yields a compatible closure. This allows building custom closures from primitives.

## Closure Union

Closure union combines two closures. The result applies both closures and takes the union.

```lean
def cloUnion (clo₁ clo₂ : Rel α → Rel α) : Rel α → Rel α :=
  fun R => clo₁ R ⊔ clo₂ R

infixl:65 " ⊔ᶜ " => cloUnion

theorem cloMono_union {clo₁ clo₂ : Rel α → Rel α}
    (h₁ : CloMono clo₁) (h₂ : CloMono clo₂) :
    CloMono (clo₁ ⊔ᶜ clo₂)

theorem wcompat_union (F : MonoRel α) {clo₁ clo₂ : Rel α → Rel α}
    (h₁ : WCompatible F clo₁) (h₂ : WCompatible F clo₂) :
    WCompatible F (clo₁ ⊔ᶜ clo₂)
```

These lemmas show closure union preserves monotonicity and weak compatibility. This helps when combining multiple up-to techniques.

### Idempotence

Several closures are idempotent. Applying them twice is the same as applying once.

```lean
theorem reflClosure_idem (R : Rel α) : reflClosure (reflClosure R) = reflClosure R
theorem symmClosure_idem (R : Rel α) : symmClosure (symmClosure R) = symmClosure R
theorem eqvClosure_idem (R : Rel α) : eqvClosure (eqvClosure R) = eqvClosure R
```

Idempotence simplifies reasoning about nested closure applications.

## Example: Up-To Reflexivity

This example proves a property using up-to reflexivity.

```lean
def EqF : MonoRel α :=
  ⟨fun R x y => x = y ∨ R x y, by
    intro R S hRS x y hxy
    cases hxy with
    | inl heq => exact Or.inl heq
    | inr hR => exact Or.inr (hRS x y hR)
  ⟩

-- EqF is reflexive when R is reflexive
theorem EqF_refl (R : Rel α) (hR : ∀ x, R x x) : ∀ x, EqF R x x :=
  fun x => Or.inl rfl
```

Since `EqF` preserves reflexivity, `reflClosure` is compatible with `EqF`. You can use up-to reflexivity in proofs involving `EqF`.

## Example: Up-To Transitivity

For transitivity arguments, use `transClosure` or `rtClosure`. You must verify compatibility holds for your specific F.

Transitivity is sound when F distributes over transitive chains. The step function can return chains of intermediate elements, and the closure accumulates them for later justification.


## Respectfulness Variants

The library provides three forms of respectfulness. Each offers a weaker condition than compatibility that is easier to verify.

`WRespectful` (weak respectfulness) requires that applying the closure to a relation l yields something in F of the rclo-expanded relation. This is the weakest form. Use it when you only need basic closure properties.

`PRespectful` (paco respectfulness) strengthens WRespectful by requiring the result lands in paco rather than just F. This variant integrates better with accumulator-based proofs.

`GRespectful` (generalized respectfulness) works with the companion closure. It provides the strongest guarantees and is useful for complex up-to arguments.

## When to Use Respectfulness

Respectfulness is useful when direct compatibility is hard to prove. The condition `clo (F R) ≤ F (clo R)` required by compatibility can be difficult to establish for some closures.

Respectfulness relaxes this by allowing the closure to interact with the paco structure. The trade-off is that respectfulness requires additional assumptions about the generator F.

For generators that are inflationary (where `R ≤ F R`), respectfulness conditions are often easier to verify. The library provides lemmas connecting respectfulness to compatibility under these assumptions.

