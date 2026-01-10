import Paco

/-!
# New Features Tests

Tests for newly added features:
- GPaco tactics (ginit, gstep, gbase, gfinal, gclo)
- Closure union operations
- Coq naming aliases
-/

namespace Paco.Tests.NewFeatures

open Paco

variable (α : Type)

/-- Simple transformer for testing -/
def TestF : MonoRel α :=
  ⟨fun R x y => x = y ∨ R x y, by
    intro R S hRS x y hxy
    cases hxy with
    | inl heq => exact Or.inl heq
    | inr hR => exact Or.inr (hRS x y hR)
  ⟩

/-!
## Closure Union Tests
-/

/-- Test cloUnion definition -/
example (R : Rel α) (x y : α) (h : reflClosure R x y) :
    (reflClosure ⊔ᶜ symmClosure) R x y :=
  Or.inl h

/-- Test cloUnion with right closure -/
example (R : Rel α) (x y : α) (h : symmClosure R x y) :
    (reflClosure ⊔ᶜ symmClosure) R x y :=
  Or.inr h

/-- Test cloMono_union -/
theorem test_cloMono_union : CloMono (reflClosure (α := α) ⊔ᶜ symmClosure) :=
  cloMono_union reflClosure_mono symmClosure_mono

/-!
## Coq Naming Alias Tests
-/

/-- Test paco_mult alias -/
theorem test_paco_mult (x y : α) (h : paco (TestF α) (paco (TestF α) ⊥) x y) :
    paco (TestF α) ⊥ x y :=
  paco_mult (TestF α) ⊥ x y h

/-- Test paco_mult_strong alias -/
theorem test_paco_mult_strong (x y : α) (h : paco (TestF α) (upaco (TestF α) ⊥) x y) :
    paco (TestF α) ⊥ x y :=
  paco_mult_strong (TestF α) ⊥ x y h

/-- Test paco_destruct alias -/
theorem test_paco_destruct (x y : α) (h : paco (TestF α) ⊥ x y) :
    (TestF α) (upaco (TestF α) ⊥) x y :=
  paco_destruct (TestF α) ⊥ x y h

/-- Test paco_construct alias -/
theorem test_paco_construct (x : α) : paco (TestF α) ⊥ x x :=
  paco_construct (TestF α) ⊥ x x (Or.inl rfl)

/-- Test paco_monotone alias -/
theorem test_paco_monotone (x y : α) (r s : Rel α) (hrs : r ≤ s)
    (h : paco (TestF α) r x y) : paco (TestF α) s x y :=
  paco_monotone (TestF α) hrs x y h

/-- Test upaco_monotone alias -/
theorem test_upaco_monotone (x y : α) (r s : Rel α) (hrs : r ≤ s)
    (h : upaco (TestF α) r x y) : upaco (TestF α) s x y :=
  upaco_monotone (TestF α) hrs x y h

/-!
## GPaco Tactic Tests

These test the new gpaco tactics: gbase, gfinal, gclo.
-/

/-- Test gbase: use base relation in gpaco_clo proof -/
theorem test_gbase (x y : α) (hr : (fun a b => a = b) x y) :
    gpaco_clo (TestF α) id (fun a b => a = b) ⊥ x y := by
  gbase
  exact hr

/-- Test gstep with rclo.base: take one step by applying F and rclo.base -/
theorem test_gstep_pattern (x : α) : gpaco_clo (TestF α) id ⊥ ⊥ x x := by
  gstep
  simp only [composeRclo_def, rclo.rclo_id]
  exact Or.inl rfl

/-!
## Closure Containment Tests
-/

/-- Test le_reflClosure -/
theorem test_le_reflClosure (R : Rel α) (x y : α) (h : R x y) : reflClosure R x y :=
  le_reflClosure R x y h

/-- Test le_symmClosure -/
theorem test_le_symmClosure (R : Rel α) (x y : α) (h : R x y) : symmClosure R x y :=
  le_symmClosure R x y h

/-- Test le_transClosure -/
theorem test_le_transClosure (R : Rel α) (x y : α) (h : R x y) : transClosure R x y :=
  le_transClosure R x y h

/-- Test le_rtClosure -/
theorem test_le_rtClosure (R : Rel α) (x y : α) (h : R x y) : rtClosure R x y :=
  le_rtClosure R x y h

/-- Test le_eqvClosure -/
theorem test_le_eqvClosure (R : Rel α) (x y : α) (h : R x y) : eqvClosure R x y :=
  le_eqvClosure R x y h

/-!
## Closure Idempotence Tests
-/

/-- Test reflClosure_idem -/
theorem test_reflClosure_idem (R : Rel α) :
    reflClosure (reflClosure R) = reflClosure R :=
  reflClosure_idem R

/-- Test symmClosure_idem -/
theorem test_symmClosure_idem (R : Rel α) :
    symmClosure (symmClosure R) = symmClosure R :=
  symmClosure_idem R

/-- Test transClosure_idem -/
theorem test_transClosure_idem (R : Rel α) :
    transClosure (transClosure R) = transClosure R :=
  transClosure_idem R

/-- Test rtClosure_idem -/
theorem test_rtClosure_idem (R : Rel α) :
    rtClosure (rtClosure R) = rtClosure R :=
  rtClosure_idem R

/-- Test eqvClosure_idem -/
theorem test_eqvClosure_idem (R : Rel α) :
    eqvClosure (eqvClosure R) = eqvClosure R :=
  eqvClosure_idem R

/-!
## Closure Absorption Tests
-/

/-- Test rtClosure_reflClosure -/
theorem test_rtClosure_reflClosure (R : Rel α) :
    rtClosure (reflClosure R) = rtClosure R :=
  rtClosure_reflClosure R

/-- Test rtClosure_transClosure -/
theorem test_rtClosure_transClosure (R : Rel α) :
    rtClosure (transClosure R) = rtClosure R :=
  rtClosure_transClosure R

/-- Test eqvClosure_reflClosure -/
theorem test_eqvClosure_reflClosure (R : Rel α) :
    eqvClosure (reflClosure R) = eqvClosure R :=
  eqvClosure_reflClosure R

/-- Test eqvClosure_symmClosure -/
theorem test_eqvClosure_symmClosure (R : Rel α) :
    eqvClosure (symmClosure R) = eqvClosure R :=
  eqvClosure_symmClosure R

/-!
## Closure Composition Tests
-/

/-- Test cloMono_comp -/
theorem test_cloMono_comp : CloMono (reflClosure (α := α) ∘ symmClosure) :=
  cloMono_comp reflClosure_mono symmClosure_mono

end Paco.Tests.NewFeatures
