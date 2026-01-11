# Differences from Coq Paco

This document describes the key architectural differences between paco-lean and the [Coq paco library](https://github.com/snu-sf/paco). Understanding these differences helps developers choose appropriate proof strategies when working with paco-lean.

## Overview

Paco-lean follows the Coq paco library closely in its core definitions. The `paco`, `upaco`, `gpaco`, and `rclo` constructions match their Coq counterparts. Both libraries provide full proving power for coinductive proofs with up-to techniques.

The key architectural difference is in how each library characterizes sound up-to techniques. Coq paco provides several sufficient conditions (wrespectfulN, prespectfulN, grespectfulN) that are known to imply compatibility. Paco-lean uses bisimulation to encode the exact boundary of what constitutes a sound up-to technique. This gives users a direct characterization rather than a collection of patterns to match.

## Proof Paths Comparison

Coq paco provides a single implicit path from respectfulness to compatibility. The proof term structure handles branch tracking automatically. Users prove the weak conditions and the library derives compatibility.

Paco-lean provides multiple explicit paths. Users choose the path that best fits their use case. The paths differ in their hypotheses and assumptions.

| Path                   | Hypothesis                             | Extra Assumptions                       |
|------------------------|----------------------------------------|-----------------------------------------|
| Strong respectfulness  | `PRespectfulStrong`                    | None                                    |
| Inflationary generator | `PRespectfulStrong` + `Inflationary F` | None (auto instance)                    |
| Tagged tracking        | `PRespectful`                          | `TagRoundtrip` + `PrespectRightGuarded` |
| Direct compatibility   | `Compatible'`                          | `ExtCompatImpliesCompat`                |

The strong respectfulness path requires no extra assumptions. For inflationary generators, which include most practical examples, automatic instances handle the assumptions.

## Strong vs Weak Conditions

Coq paco uses weak respectfulness conditions with conjunctive hypotheses. The condition `prespectfulN` requires both `l ≤ r` and `l ≤ gf r` to conclude that `clo l` lands in `paco`.

Paco-lean provides both weak and strong variants. The strong variant `PRespectfulStrong` uses a disjunctive hypothesis `l ≤ r ⊔ F r` directly.

```lean
-- Weak form (matches Coq, requires tagged assumptions)
structure PRespectful (F : MonoRel α) (clo : Rel α → Rel α) : Prop where
  mon : CloMono clo
  respect : ∀ l r, l ≤ r → l ≤ F r → clo l ≤ paco F (r ⊔ clo r)

-- Strong form (no extra assumptions needed)
structure PRespectfulStrong (F : MonoRel α) (clo : Rel α → Rel α) : Prop where
  mon : CloMono clo
  respect : ∀ l r, l ≤ r ⊔ F r → clo l ≤ paco F (r ⊔ clo r)
```

The strong form directly proves `Compatible'` via `prespect_compatible'_strong`. In practice, proving the strong condition is often no harder than proving the weak condition. When your closure respects the combined relation `r ⊔ F r`, use the strong form.

## Inflationary Generators

Paco-lean distinguishes inflationary generators where `R ≤ F R` for all R. Most practical coinductive definitions are inflationary. Stream bisimulation, process equivalence, and simulation relations all have this property.

```lean
class Inflationary (F : MonoRel α) : Prop where
  h : ∀ R, R ≤ F R
```

When `Inflationary F` holds, the library provides automatic instances for `ExtCompatImpliesCompat`. This means the compatibility chain works without manual assumptions. The theorem `prespect_compatible'_inflationary` combines strong respectfulness with inflationary to derive `Compatible'` directly.

Coq paco does not distinguish inflationary generators explicitly. The property is used implicitly in proofs but not exposed as a reusable abstraction.

## Extended Generator Framework

Both libraries use an extended generator `gf' = id ⊔ gf` for compatibility proofs. The `Compatible'` condition is compatibility with this extended generator.

Paco-lean makes the extended generator explicit via `extendedGen`. The `ExtCompatImpliesCompat` assumption captures when extended-generator compatibility implies original-generator compatibility.

```lean
def extendedGen (F : MonoRel α) : MonoRel α where
  F := fun R => R ⊔ F R
  mono := fun _ _ hRS => sup_le_sup hRS (F.mono' hRS)

class ExtCompatImpliesCompat (F : MonoRel α) : Prop where
  h : ∀ clo, CloMono clo → Compatible (extendedGen F) clo → Compatible F clo
```

Two sufficient conditions provide automatic instances. Inflationary generators satisfy the assumption because the identity component adds nothing new. The `extendedGen` itself is always inflationary, providing a bootstrapping instance.

## Tagged Relation Framework

For cases requiring the weak respectfulness conditions, paco-lean provides explicit branch-tracking machinery. The `Tagged` framework marks whether elements came from the unguarded branch (R) or the guarded branch (F R).

```lean
inductive rcloTagged (clo : Rel α → Rel α) (F : MonoRel α) (R : Rel α) : Bool → Rel α where
  | base_unguarded : R x y → rcloTagged clo F R false x y
  | base_guarded : F R x y → rcloTagged clo F R true x y
  | clo_step : (∀ a c, R' a c → rcloTagged clo F R b a c) →
               clo R' x y → rcloTagged clo F R b x y
```

This machinery is only needed when using the weak `PRespectful` condition with non-inflationary generators. Most users can ignore it entirely by using the strong variants or inflationary instances.

The framework does provide value beyond respectfulness proofs. The `Tag`, `tagLeft`, `tagRight`, and projection functions form a reusable toolkit for any proof requiring explicit branch tracking.

## Bisimulation-Based Boundary Characterization

The most significant difference between the libraries is how they characterize sound up-to techniques.

Coq paco provides several sufficient conditions that are known to imply compatibility. The conditions `wrespectfulN`, `prespectfulN`, and `grespectfulN` are patterns that users can match. If a closure fits one of these patterns, the corresponding lemma proves it embeds into the companion. If a closure does not fit these patterns, users must provide an ad-hoc compatibility proof.

Paco-lean uses bisimulation to encode the exact boundary of soundness. The `TagClosed` property and the preservation lemmas characterize precisely which operations maintain the structure required for compatibility. Any closure can be checked against this characterization directly.

```lean
def TagClosed (R : Rel (Tag α)) : Prop :=
  (∀ a b, R (Sum.inl a) (Sum.inr b) → False) ∧
  (∀ a b, R (Sum.inr a) (Sum.inl b) → False)
```

The bisimulation establishes a correspondence between relations on `Tag α = Sum α α` and pairs of relations on `α`. Operations that preserve `TagClosed` respect this correspondence. The preservation lemmas (`projLeft_paco`, `prespectClosure_taggedUnion`, `upaco_closed`) show that paco operations maintain this structure.

This approach has a concrete advantage. Users do not need to fit their closure into a predefined pattern. They can verify directly whether their closure preserves the tagged structure. The bisimulation makes the boundary explicit rather than encoding it implicitly through sufficient conditions.

## Choosing a Proof Strategy

For most use cases, follow this decision process.

First, check if your generator is inflationary (`R ≤ F R`). If yes, use `PRespectfulStrong` with the automatic `Inflationary` instance. This path requires no manual assumptions.

If not inflationary, try proving `PRespectfulStrong` directly. The disjunctive hypothesis often works without needing to split cases. The theorem `prespect_compatible'_strong` gives you `Compatible'` immediately.

If the strong form is difficult, use `PRespectful` with explicit `TagRoundtrip` and `PrespectRightGuarded` instances. For direct compatibility proofs, use `Compatible'` with `compatible'_le_companion`.

## Summary

| Aspect                  | Coq Paco                     | Paco-Lean                        |
|-------------------------|------------------------------|----------------------------------|
| Core definitions        | Direct                       | Direct (matching)                |
| Up-to boundary          | Sufficient conditions        | Exact characterization           |
| Soundness check         | Match predefined patterns    | Verify TagClosed preservation    |
| Proof paths             | Single implicit              | Multiple explicit                |
| Weak conditions         | Work directly                | Require tagged assumptions       |
| Strong conditions       | Not distinguished            | Work without assumptions         |
| Inflationary generators | Implicit                     | Explicit with auto instances     |
| Branch tracking         | Via proof terms              | Via bisimulation framework       |

## References

See [Architecture Guide](03-architecture.md) for the module structure. See [Up-To Techniques Guide](06-upto-guide.md) for usage of closures and respectfulness. The Coq paco library documentation provides additional context for the original design.
