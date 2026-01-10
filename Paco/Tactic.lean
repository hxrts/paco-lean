import Paco.Basic
import Paco.GPaco
import Paco.UpTo

/-!
# Paco Tactics

This module provides tactics for working with parametrized coinduction (paco).

## Overview

The tactics mirror those in the Coq paco library:
- `pcofix`: Start a coinduction proof
- `punfold`: Unfold a paco hypothesis to expose F structure
- `pfold`: Fold F (upaco F r) into paco F r
- `pstep`: Make progress (go into paco side of upaco)
- `pbase`: Use accumulated hypothesis (r side of upaco)
- `pclearbot`: Simplify upaco F ⊥ to paco F ⊥

## Usage

```lean
theorem my_bisim : paco F ⊥ x y := by
  pcofix R ih with
  | witness => -- prove R x y
  | step a b hab =>
    -- prove F (R ⊔ ⊥) a b given R a b
```

## References

- [Paco Coq tactics](https://github.com/snu-sf/paco/blob/master/src/pacotac.v)
-/

namespace Paco

/-!
## Simp Lemmas
-/

/-- Simp lemmas for paco simplification -/
@[simp] theorem paco_sup_bot_eq {α : Type*} (F : MonoRel α) : paco F ⊥ = F.toOrderHom.gfp := paco_bot F

/-!
## Basic Tactics

These macros provide the core functionality for paco proofs.
-/

/-- `punfold h` unfolds a hypothesis `h : paco F r x y` to `h : F (upaco F r) x y`.

This exposes the F-structure of the coinductive hypothesis, allowing you to
pattern match or destruct it.

Example:
```lean
example (h : paco F r x y) : F (upaco F r) x y := by
  punfold h
  exact h
```
-/
macro "punfold" h:ident : tactic =>
  `(tactic| (have $h := Paco.paco_unfold _ _ $h))

/-- `pfold` transforms a goal `⊢ paco F r x y` into `⊢ F (upaco F r) x y`.

This lets you prove a paco goal by providing the F-structure directly.

Example:
```lean
example : paco F r x y := by
  pfold
  -- Goal is now: F (upaco F r) x y
  exact h
```
-/
macro "pfold" : tactic =>
  `(tactic| (apply Paco.paco_fold))

/-- `gpunfold h` unfolds a gpaco hypothesis `h : gpaco F r g x y` to expose structure.

After unfolding: `h : F (gupaco F r g) x y ∨ r x y`
-/
macro "gpunfold" h:ident : tactic =>
  `(tactic| (have $h := Paco.gpaco_unfold _ _ _ $h))

/-- `gpfold` transforms a goal `⊢ gpaco F r g x y` from `⊢ F (gupaco F r g) x y`.
-/
macro "gpfold" : tactic =>
  `(tactic| (apply Paco.gpaco_fold))

/-!
## Progress Tactics
-/

/-- `pstep` makes progress by going into the paco side of upaco.

When the goal is `⊢ upaco F r x y` (i.e., `paco F r x y ∨ r x y`),
`pstep` chooses the left (paco) side and then folds into F-structure.

After `pstep`: `⊢ F (upaco F r) x y`

Example:
```lean
example : upaco F r x y := by
  pstep
  -- Goal: F (upaco F r) x y
  exact h
```
-/
macro "pstep" : tactic =>
  `(tactic| (left; apply Paco.paco_fold))

/-- `pbase` uses the accumulated hypothesis (r side of upaco).

When the goal is `⊢ upaco F r x y`, `pbase` chooses the right (r) side.

After `pbase`: `⊢ r x y`

Example:
```lean
example (hr : r x y) : upaco F r x y := by
  pbase
  exact hr
```
-/
macro "pbase" : tactic =>
  `(tactic| right)

/-- `pclearbot` simplifies `upaco F ⊥` to `paco F ⊥`.

This is useful after applying paco_coind with ⊥ parameter.

Example:
```lean
example (h : upaco F ⊥ x y) : paco F ⊥ x y := by
  pclearbot at h
  exact h
```
-/
macro "pclearbot" : tactic =>
  `(tactic| (simp only [Paco.upaco_bot]))

/-- `pclearbot_hyp h` simplifies `upaco F ⊥` to `paco F ⊥` in hypothesis h. -/
macro "pclearbot_hyp" h:ident : tactic =>
  `(tactic| (simp only [Paco.upaco_bot] at $h:ident))

/-!
## Coinduction Tactics
-/

/-- `pcofix ih` starts a coinduction proof for a goal `⊢ paco F r x y`.

This applies `paco_coind` and introduces the coinductive hypothesis `ih`.
After `pcofix ih`:
- Goal becomes: `⊢ F (R ⊔ r) a b` for arbitrary `a b` with `ih : R a b`
- A preliminary goal `⊢ R x y` is also generated

Example:
```lean
theorem my_coinduction : paco F r x y := by
  pcofix ih
  · -- Prove R x y (the witness contains our starting point)
    exact trivial
  · -- Prove F (R ⊔ r) a b given ih : R a b
    ...
```
-/
macro "pcofix" ih:ident : tactic =>
  `(tactic| (
    apply Paco.paco_coind _ ?R _
    case hpost =>
      intro _ _ $ih
    case hxy => ?_
  ))

/-- `pcofix' R ih hxy hpost` applies paco_coind with explicit names.

This is a lower-level variant that gives you full control over naming:
- `R`: the witness relation (a placeholder ?R will be created)
- `ih`: name for the coinductive hypothesis
- `hxy`: name for the initial membership goal
- `hpost`: name for the post-fixpoint goal
-/
macro "pcofix'" ih:ident : tactic =>
  `(tactic| (
    refine Paco.paco_coind _ ?_ _ ?_ ?_
    intro _ _ $ih
  ))

/-- `gpcofix ih` starts a gpaco coinduction proof for a goal `⊢ gpaco F r g x y`.

Similar to `pcofix` but for generalized paco with guarded parameter.
-/
macro "gpcofix" ih:ident : tactic =>
  `(tactic| (
    apply Paco.gpaco_coind _ ?R _ _ _ _
    case hpost =>
      intro _ _ $ih
    case hxy => ?_
  ))

/-!
## Accumulation Tactics
-/

/-- `paco_acc` applies the accumulation lemma to absorb paco in the parameter.

Transforms `⊢ paco F (paco F r) x y` into `⊢ paco F r x y`.
-/
macro "paco_acc" : tactic =>
  `(tactic| (apply Paco.paco_acc))

/-- `paco_acc_upaco` applies the stronger accumulation lemma.

Transforms `⊢ paco F (upaco F r) x y` into `⊢ paco F r x y`.
-/
macro "paco_acc_upaco" : tactic =>
  `(tactic| (apply Paco.paco_acc_upaco))

/-!
## Utility Tactics
-/

/-- `paco_mon h` applies monotonicity of paco.

Given `h : r ≤ s`, transforms `⊢ paco F s x y` from `⊢ paco F r x y`.
-/
macro "paco_mon" h:term : tactic =>
  `(tactic| (apply Paco.paco_mon _ $h))

/-- `upaco_mon h` applies monotonicity of upaco.

Given `h : r ≤ s`, transforms `⊢ upaco F s x y` from `⊢ upaco F r x y`.
-/
macro "upaco_mon" h:term : tactic =>
  `(tactic| (apply Paco.upaco_mon _ $h))

/-!
## GPaco with Closures Tactics

These tactics work with `gpaco_clo` and `gupaco_clo` for up-to reasoning.
-/

/-- `ginit` initializes a gpaco proof by embedding paco into gupaco_clo with companion.

Transforms `⊢ paco F r x y` into `⊢ gupaco_clo F (companion F) r x y`.

This is the entry point for up-to proofs using the companion closure.
-/
macro "ginit" : tactic =>
  `(tactic| (apply Paco.paco_le_gpaco_clo))

/-- `gstep` takes one step in a gpaco_clo proof by applying F.

When the goal is `⊢ gpaco_clo F clo r rg x y`, `gstep` allows you to make
progress by providing `F (gupaco_clo F clo r) x y ∨ r x y`.
-/
macro "gstep" : tactic =>
  `(tactic| (apply Paco.rclo.base; left; apply Paco.paco_fold))

/-- `gbase` uses the base relation in a gpaco_clo proof.

When the goal is `⊢ gpaco_clo F clo r rg x y`, `gbase` lets you prove
`r x y` directly.
-/
macro "gbase" : tactic =>
  `(tactic| (apply Paco.r_le_gpaco_clo))

/-- `gfinal` concludes a gpaco_clo proof by showing it reduces to standard paco.

Applies `gpaco_clo_final` which requires compatibility of the closure.
-/
macro "gfinal" : tactic =>
  `(tactic| (apply Paco.gpaco_clo_final))

/-- `gclo` applies the closure operator in a gpaco_clo proof.

This lets you use the up-to technique by applying the closure.
-/
macro "gclo" : tactic =>
  `(tactic| (apply Paco.rclo.clo))

end Paco
