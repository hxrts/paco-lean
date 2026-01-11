# Theoretical Foundations

This document explains the mathematical concepts underlying parametrized coinduction.

## Standard Coinduction

Coinduction proves properties about infinite structures by showing a relation is contained in a greatest fixed point. The Knaster-Tarski theorem characterizes the greatest fixed point of a monotone function F as the union of all post-fixed points.

```
gfp F = ⋃ { R | R ⊆ F(R) }
```

A relation R is a post-fixed point when `R ⊆ F(R)`. This means every pair in R can be justified by one application of F. To prove `gfp F x y`, you provide a witness relation R such that `R x y` and `R ⊆ F(R)`.

This approach requires knowing the complete witness relation upfront. Every pair you want to prove related must be in R before you begin. This creates difficulties when the set of pairs grows during a proof.

## The Accumulation Problem

Consider proving transitivity for a coinductive relation. Given `x ~ y` and `y ~ z`, you want to show `x ~ z`. The witness relation must include all intermediate pairs.

For a chain `x₀ ~ x₁ ~ x₂ ~ xₙ`, standard coinduction requires predicting every `xᵢ ~ xⱼ` pair that will arise. The number of such pairs grows quadratically with chain length, and the witness relation becomes impossible to specify for infinite chains.

This is the accumulation problem. Standard coinduction cannot accumulate new facts during a proof. You must know everything before starting.

## Parametrized Coinduction

Parametrized coinduction solves the accumulation problem by adding a parameter to the fixed point. The parameter holds facts that can be assumed during the proof.

```
paco F r = gfp (λ R. F(R ∪ r))
```

The relation `r` is the accumulator. The generating function `λ R. F(R ∪ r)` allows using facts from both the coinductive hypothesis R and the accumulator r.

The usable coinductive hypothesis becomes `upaco F r = paco F r ∪ r`. When you need to make a recursive call, you can appeal to either `paco F r` or directly to facts in r.

### Key Properties

The key properties describe accumulation, monotonicity, and the empty accumulator case.

```lean
theorem paco_acc (F : MonoRel α) (r : Rel α) :
    paco F (paco F r) ≤ paco F r

theorem paco_mon (F : MonoRel α) {r s : Rel α} (hrs : r ≤ s) :
    paco F r ≤ paco F s

theorem paco_bot (F : MonoRel α) : paco F ⊥ = F.toOrderHom.gfp
```

The accumulation lemma shows nested `paco` can be folded. The monotonicity lemma shows larger accumulators give larger results. The empty accumulator lemma shows paco reduces to the greatest fixed point.

## Generalized Paco

Generalized paco adds a second parameter for guarded facts. The parameter `r` holds immediate facts and `g` holds facts available after one `F` step.

```
gpaco F r g = paco F (r ∪ g) ∪ r

gupaco F r g = gpaco F r g ∪ g
```

The guard prevents immediate use of facts in `g`. The usable hypothesis is `gupaco`, which releases the guard after one step.

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

The companion is the greatest compatible monotone closure operator. It is defined as the supremum over all closures that are both monotone and compatible with F.

```lean
def companion (F : MonoRel α) : Rel α → Rel α :=
  ⨆ clo, (· : { clo // CloMono clo ∧ Compatible F clo}).val
```

The companion subsumes all other compatible closures. If a closure `clo` is compatible with F, then `clo R ≤ companion F R` for all R. This makes the companion a universal choice.

The companion satisfies three key properties. It is extensive, meaning `R ≤ companion F R`. It is compatible with F. It absorbs gupaco, meaning `gupaco_clo F (companion F) R ≤ companion F R`.

In practice, the companion is useful when you do not know which specific closure to use. By choosing the companion, you get the maximum up-to reasoning power without committing to a particular closure.

## References

The theoretical foundations of paco come from academic research on coinduction and bisimulation.

- Hur et al. "The Power of Parameterization in Coinductive Proof" (POPL 2013) introduces parametrized coinduction
- Hur et al. "An Equational Theory for Weak Bisimulation via Generalized Parameterized Coinduction" (CPP 2020) introduces gpaco
- Pous and Sangiorgi "Enhancements of the bisimulation proof method" covers up-to techniques
