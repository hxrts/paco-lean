import Paco

/-!
# GPaco with Closure Tests

Tests for gpaco_clo and up-to techniques.
-/

namespace Paco.Tests.GPacoClo

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
## gpaco_clo basic tests
-/

/-- r injects into gpaco_clo -/
theorem test_r_le_gpaco_clo (r rg : Rel α) (x y : α) (hr : r x y) :
    gpaco_clo (TestF α) id r rg x y :=
  r_le_gpaco_clo (TestF α) id r rg x y hr

/-- Identity closure reduces gpaco_clo to standard form -/
theorem test_gpaco_clo_id (r rg : Rel α) :
    gpaco_clo (TestF α) id r rg = paco (TestF α) (rg ⊔ r) ⊔ r :=
  gpaco_clo_id (TestF α) r rg

/-- paco injects into gpaco_clo -/
theorem test_paco_le_gpaco_clo (r rg : Rel α) (x y : α)
    (h : paco (composeRclo (TestF α) id) (rg ⊔ r) x y) :
    gpaco_clo (TestF α) id r rg x y :=
  paco_le_gpaco_clo (TestF α) id r rg x y h

/-!
## Companion tests
-/

/-- Companion is extensive -/
theorem test_companion_extensive (R : Rel α) : R ≤ companion (TestF α) R :=
  companion_extensive (TestF α) R

/-- Companion is compatible -/
theorem test_companion_compat : Compatible (TestF α) (companion (TestF α)) :=
  companion_compat (TestF α)

/-- Companion is monotone -/
theorem test_companion_mono : Monotone2 (companion (TestF α)) :=
  companion_mono (TestF α)

/-- Companion absorbs gupaco -/
theorem test_companion_gupaco (R : Rel α) :
    gupaco_clo (TestF α) (companion (TestF α)) R ≤ companion (TestF α) R :=
  companion_gupaco (TestF α) R

/-- Companion gupaco equality -/
theorem test_companion_gupaco_eq (R : Rel α) :
    gupaco_clo (TestF α) (companion (TestF α)) R = companion (TestF α) R :=
  companion_gupaco_eq (TestF α) R

/-!
## Monotonicity tests
-/

/-- gpaco_clo is monotone in r -/
theorem test_gpaco_clo_mon_r (clo : Rel α → Rel α) (rg : Rel α)
    {r r' : Rel α} (hr : r ≤ r') :
    gpaco_clo (TestF α) clo r rg ≤ gpaco_clo (TestF α) clo r' rg :=
  gpaco_clo_mon_r (TestF α) clo rg hr

/-- gpaco_clo is monotone in rg -/
theorem test_gpaco_clo_mon_rg (clo : Rel α → Rel α) (r : Rel α)
    {rg rg' : Rel α} (hrg : rg ≤ rg') :
    gpaco_clo (TestF α) clo r rg ≤ gpaco_clo (TestF α) clo r rg' :=
  gpaco_clo_mon_rg (TestF α) clo r hrg

/-!
## Coinduction principle tests
-/

/-- Test gpaco_clo_cofix: direct coinduction -/
theorem test_gpaco_clo_cofix (x : α) : gpaco_clo (TestF α) id ⊥ ⊥ x x := by
  apply gpaco_clo_cofix (TestF α) id ⊥ ⊥ (fun a b => a = b)
  · intro a b heq
    left
    simp only [rclo.rclo_id, Rel.sup_bot]
    left; subst heq; rfl
  · rfl

/-- Test gpaco_clo_coind: general coinduction principle -/
theorem test_gpaco_clo_coind (x : α) : gpaco_clo (TestF α) id ⊥ ⊥ x x := by
  apply gpaco_clo_coind (TestF α) id ⊥ ⊥ (fun a b => a = b)
  intro rr _INC _CIH
  intro a b heq
  apply rclo.base
  left
  apply paco_coind (composeRclo (TestF α) id) (fun u v => u = v) (rr ⊔ ⊥)
  · intro u v huv
    simp only [composeRclo_def, rclo.rclo_id, Rel.sup_bot]
    left; exact huv
  · exact heq
  · rfl

/-- Test gpaco_clo_coind': pointwise coinduction principle -/
theorem test_gpaco_clo_coind' (x : α) : gpaco_clo (TestF α) id ⊥ ⊥ x x := by
  apply gpaco_clo_coind' (TestF α) id ⊥ ⊥ (fun a b => a = b)
  · intro rr _INC _CIH a b heq
    apply rclo.base
    left
    apply paco_coind (composeRclo (TestF α) id) (fun u v => u = v) (rr ⊔ ⊥)
    · intro u v huv
      simp only [composeRclo_def, rclo.rclo_id, Rel.sup_bot]
      left; exact huv
    · exact heq
  · rfl

/-- Test that gpaco_clo_coind' produces the expected coinduction goal -/
theorem test_gpaco_clo_coind'_goal (x : α) : gpaco_clo (TestF α) id ⊥ ⊥ x x := by
  -- The witness relation is equality
  refine gpaco_clo_coind' (TestF α) id ⊥ ⊥ (fun a b => a = b) ?OBG ?hxy
  case OBG =>
    intro rr _INC _CIH a b heq
    apply rclo.base
    left
    apply paco_coind (composeRclo (TestF α) id) (fun u v => u = v) (rr ⊔ ⊥)
    · intro u v huv
      simp only [composeRclo_def, rclo.rclo_id, Rel.sup_bot]
      left; exact huv
    · exact heq
  case hxy =>
    rfl

/-!
## Closure composition tests
-/

/-- Identity with any closure is that closure -/
theorem test_id_comp_clo (clo : Rel α → Rel α) : id ∘ clo = clo := rfl

/-- Any closure with identity is that closure -/
theorem test_clo_comp_id (clo : Rel α → Rel α) : clo ∘ id = clo := rfl

/-!
## rclo basic tests
-/

/-- rclo base injection -/
theorem test_rclo_base (clo : Rel α → Rel α) (R : Rel α) : R ≤ rclo clo R :=
  rclo.base_le

/-- rclo is closed under clo -/
theorem test_rclo_clo (clo : Rel α → Rel α) (R : Rel α) : clo (rclo clo R) ≤ rclo clo R :=
  rclo.clo_rclo

/-- rclo is idempotent -/
theorem test_rclo_rclo (clo : Rel α → Rel α) (R : Rel α) : rclo clo (rclo clo R) ≤ rclo clo R :=
  fun x y h => rclo.rclo_rclo x y h

/-- rclo with id is identity -/
theorem test_rclo_id (R : Rel α) : rclo id R = R :=
  @rclo.rclo_id α R

end Paco.Tests.GPacoClo
