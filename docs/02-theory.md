# Theoretical Foundations

This document explains the mathematical concepts underlying parametrized coinduction.

## Standard Coinduction

Coinduction proves properties about infinite structures by showing a relation is contained in a greatest fixed point. The Knaster-Tarski theorem characterizes the greatest fixed point of a monotone function F as the union of all post-fixed points.

```
gfp F = ⋃ { R | R ⊆ F(R) }
```

A relation R is a post-fixed point when `R ⊆ F(R)`. To prove `gfp F x y`, you provide a witness relation R such that `R x y` and `R ⊆ F(R)`.

This approach requires knowing the complete witness relation upfront. Every pair you want to prove related must be in R before you begin. This creates difficulties when the set of pairs grows during a proof.

## The Accumulation Problem

Consider proving transitivity for a coinductive relation. Given `x ~ y` and `y ~ z`, you want to show `x ~ z`. The witness relation must include all intermediate pairs.

For a chain `x₀ ~ x₁ ~ x₂ ~ ... ~ xₙ`, standard coinduction requires predicting every `xᵢ ~ xⱼ` pair that will arise. The number of such pairs grows quadratically with chain length. In infinite chains, the witness relation becomes impossible to specify.

This is the accumulation problem. Standard coinduction cannot accumulate new facts during a proof. You must know everything before starting.

## Parametrized Coinduction

Parametrized coinduction solves the accumulation problem by adding a parameter to the fixed point. The parameter holds facts that can be assumed during the proof.

```
paco F r = gfp (λ R. F(R ∪ r))
```

The relation `r` is the accumulator. The generating function `λ R. F(R ∪ r)` allows using facts from both the coinductive hypothesis R and the accumulator r.

The usable coinductive hypothesis becomes `upaco F r = paco F r ∪ r`. When you need to make a recursive call, you can appeal to either `paco F r` or directly to facts in r.

### Key Properties

The accumulation theorem states that `paco F (paco F r) ≤ paco F r`. You can fold a nested paco into a single paco. This means proving `paco F (paco F r) x y` is equivalent to proving `paco F r x y`.

```lean
theorem paco_acc (F : MonoRel α) (r : Rel α) :
    paco F (paco F r) ≤ paco F r
```

This theorem enables incremental proofs. After establishing `paco F r x y`, you can use this fact in subsequent coinductive arguments by placing it in the accumulator.

Monotonicity states that `paco F` is monotone in both arguments. If `r ≤ s`, then `paco F r ≤ paco F s`. Larger accumulators give larger results.

```lean
theorem paco_mon (F : MonoRel α) {r s : Rel α} (hrs : r ≤ s) :
    paco F r ≤ paco F s
```

When the accumulator is empty, paco reduces to the standard greatest fixed point.

```lean
theorem paco_bot (F : MonoRel α) : paco F ⊥ = F.toOrderHom.gfp
```

This shows paco generalizes standard coinduction.

## Generalized Paco

Generalized paco (gpaco) adds a second parameter for guarded facts. The first parameter `r` contains facts available immediately. The second parameter `g` contains facts available only after one step of F.

```
gpaco F r g = paco F (r ∪ g) ∪ r
```

The guard `g` prevents using certain facts until you have made progress. After unfolding once, guarded facts become available. This distinction matters for proofs where immediate use of some facts would create unsound reasoning.

The usable hypothesis for gpaco releases the guard.

```
gupaco F r g = gpaco F r g ∪ g
```

After one F-step, both `r` and `g` become available.

### Relationship to Paco

When the guard is empty, gpaco reduces to upaco.

```lean
theorem gpaco_bot_g (F : MonoRel α) (r : Rel α) :
    gpaco F r ⊥ = upaco F r
```

When both parameters are equal, gpaco also simplifies.

```lean
theorem gpaco_diag (F : MonoRel α) (r : Rel α) :
    gpaco F r r = upaco F r
```

These properties show gpaco is a strict generalization of paco.

## Up-To Techniques

Up-to techniques enhance coinductive proofs by allowing reasoning "up to" some closure operation. Instead of proving `R ⊆ F(R)`, you prove `R ⊆ F(clo(R))` for some closure operator `clo`.

A closure operator is compatible with F when `clo(F(R)) ⊆ F(clo(R))` for all R. Compatibility ensures the closure does not add pairs that F cannot justify.

```lean
def Compatible (F : MonoRel α) (clo : Rel α → Rel α) : Prop :=
  ∀ R, clo (F R) ≤ F (clo R)
```

Standard closures include reflexive closure, symmetric closure, transitive closure, and equivalence closure. Each is compatible with appropriate classes of relation transformers.

### The Companion

The companion is the greatest compatible monotone closure operator. It subsumes all other compatible closures.

```lean
def companion (F : MonoRel α) : Rel α → Rel α :=
  ⨆ clo, (· : { clo // CloMono clo ∧ Compatible F clo}).val
```

The companion satisfies several key properties. It is extensive, meaning `R ≤ companion F R`. It is compatible with F. It absorbs `gupaco`, meaning `gupaco_clo F (companion F) R ≤ companion F R`.

Using the companion as your closure operator gives the most powerful up-to reasoning available for a given F.

## References

The theoretical foundations of paco come from academic research on coinduction and bisimulation.

- Hur et al. "The Power of Parameterization in Coinductive Proof" (POPL 2013) introduces parametrized coinduction
- Hur et al. "An Equational Theory for Weak Bisimulation via Generalized Parameterized Coinduction" (CPP 2020) introduces gpaco
- Pous and Sangiorgi "Enhancements of the bisimulation proof method" covers up-to techniques
