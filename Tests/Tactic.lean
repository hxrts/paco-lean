import Paco

/-!
# Paco Tactic Tests

Tests for paco theorems and tactics.
Note: Some macro-based tactics have limitations that are documented here.
-/

namespace Paco.Tests.Tactic

open Paco

variable (α : Type)

/-!
## Test Setup: Simple Relation Transformer

A simple transformer for testing: relates x y if they're equal or R x y.
This gives us an easy F to work with.
-/

/-- Simple transformer: equality or R -/
def TestF : MonoRel α :=
  ⟨fun R x y => x = y ∨ R x y, by
    intro R S hRS x y hxy
    cases hxy with
    | inl heq => exact Or.inl heq
    | inr hR => exact Or.inr (hRS x y hR)
  ⟩

/-!
## paco_unfold/paco_fold tests (using theorems directly)
-/

/-- Test paco_unfold theorem -/
theorem test_paco_unfold (x y : α) (h : paco (TestF α) ⊥ x y) :
    (TestF α) (upaco (TestF α) ⊥) x y :=
  paco_unfold (TestF α) ⊥ x y h

/-- Test paco_fold theorem -/
theorem test_paco_fold (x : α) : paco (TestF α) ⊥ x x :=
  paco_fold (TestF α) ⊥ x x (Or.inl rfl)

/-!
## pfold tactic tests
-/

/-- Test pfold: folds F into paco -/
theorem test_pfold (x : α) : paco (TestF α) ⊥ x x := by
  pfold
  exact Or.inl rfl

/-!
## pstep tests
-/

/-- Test pstep: progress via paco side of upaco -/
theorem test_pstep (x : α) : upaco (TestF α) ⊥ x x := by
  pstep
  exact Or.inl rfl

/-!
## pbase tests
-/

/-- Test pbase: use r side of upaco -/
theorem test_pbase (x y : α) (hr : (fun a b => a = b) x y) :
    upaco (TestF α) (fun a b => a = b) x y := by
  pbase
  exact hr

/-!
## pclearbot tests
-/

/-- Test pclearbot: simplify upaco F ⊥ to paco F ⊥ in goal -/
theorem test_pclearbot_goal (x y : α) (h : paco (TestF α) ⊥ x y) : upaco (TestF α) ⊥ x y := by
  pclearbot
  exact h

/-!
## paco_coind theorem tests
-/

/-- Test paco_coind directly -/
theorem test_paco_coind (x : α) : paco (TestF α) ⊥ x x := by
  apply paco_coind (TestF α) (fun a b => a = b) ⊥
  · intro a b heq
    simp only [Rel.sup_bot]
    exact Or.inl heq
  · rfl

/-- Test paco_coind with a custom witness -/
theorem test_paco_coind_custom {R : Rel α} (hR : ∀ a b, R a b → (TestF α) R a b)
    (x y : α) (hxy : R x y) : paco (TestF α) ⊥ x y := by
  apply paco_coind (TestF α) R ⊥
  · intro a b hab
    simp only [Rel.sup_bot]
    exact hR a b hab
  · exact hxy

/-!
## GPaco theorem tests
-/

/-- Test gpaco_unfold theorem -/
theorem test_gpaco_unfold (x y : α) (h : gpaco (TestF α) ⊥ ⊥ x y) :
    (TestF α) (gupaco (TestF α) ⊥ ⊥) x y ∨ (⊥ : Rel α) x y :=
  gpaco_unfold (TestF α) ⊥ ⊥ x y h

/-- Test gpaco_fold theorem -/
theorem test_gpaco_fold (x : α) : gpaco (TestF α) ⊥ ⊥ x x :=
  gpaco_fold (TestF α) ⊥ ⊥ x x (Or.inl rfl)

/-- Test gpfold tactic -/
theorem test_gpfold (x : α) : gpaco (TestF α) ⊥ ⊥ x x := by
  gpfold
  exact Or.inl rfl

/-!
## Accumulation theorem tests
-/

/-- Test paco_acc theorem -/
theorem test_paco_acc (x y : α) (h : paco (TestF α) (paco (TestF α) ⊥) x y) :
    paco (TestF α) ⊥ x y :=
  paco_acc (TestF α) ⊥ x y h

/-- Test paco_acc_upaco theorem -/
theorem test_paco_acc_upaco (x y : α) (h : paco (TestF α) (upaco (TestF α) ⊥) x y) :
    paco (TestF α) ⊥ x y :=
  paco_acc_upaco (TestF α) ⊥ x y h

/-!
## Monotonicity theorem tests
-/

/-- Test paco_mon theorem -/
theorem test_paco_mon (x y : α) (r s : Rel α) (hrs : r ≤ s) (h : paco (TestF α) r x y) :
    paco (TestF α) s x y :=
  paco_mon (TestF α) hrs x y h

/-- Test upaco_mon theorem -/
theorem test_upaco_mon (x y : α) (r s : Rel α) (hrs : r ≤ s) (h : upaco (TestF α) r x y) :
    upaco (TestF α) s x y :=
  upaco_mon (TestF α) hrs x y h

/-!
## Combined usage
-/

/-- Realistic example: prove transitivity-like property -/
theorem test_combined (x y z : α) (hxy : x = y) (hyz : y = z) :
    paco (TestF α) ⊥ x z := by
  pfold
  subst hxy hyz
  exact Or.inl rfl

/-- Test using gpaco with base case -/
theorem test_gpaco_base (x y : α) (h : (fun a b => a = b) x y) :
    gpaco (TestF α) (fun a b => a = b) ⊥ x y := by
  right  -- Use the r (base) side
  exact h

end Paco.Tests.Tactic
