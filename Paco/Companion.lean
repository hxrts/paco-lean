import Paco.UpTo.WCompat

/-!
# Companion Interface

This module provides a small, packaged interface for the companion operator.
It reuses the `cpn` construction from the up-to framework and packages the
expected fields (monotonicity, compatibility, and extensiveness).
-/

namespace Paco

variable {α : Type*}

/-- A packaged companion for a relation transformer. -/
structure Companion (F : MonoRel α) where
  /-- The companion closure operator. -/
  C : Rel α → Rel α
  /-- Monotonicity of the closure. -/
  mono : Monotone2 C
  /-- Compatibility with the generator. -/
  compat : Compatible F C
  /-- Extensiveness: R ≤ C R. -/
  extensive : ∀ R, R ≤ C R

/-!
## Canonical companion (cpn) and convenience lemmas
-/

/-- Canonical companion closure operator. -/
def companion (F : MonoRel α) : Rel α → Rel α := cpn F

/-- The canonical companion built from `cpn`. -/
def cpnCompanion (F : MonoRel α) : Companion F where
  C := companion F
  mono := cpn.cpn_cloMono
  compat := cpn.compat
  extensive := fun R => cpn.base (F := F) (R := R)

@[simp]
theorem cpnCompanion_C (F : MonoRel α) : (cpnCompanion F).C = companion F := rfl

@[simp]
theorem companion_def (F : MonoRel α) : companion F = cpn F := rfl

theorem companion_mono (F : MonoRel α) : Monotone2 (companion F) :=
  cpn.cpn_cloMono

theorem companion_extensive (F : MonoRel α) (R : Rel α) : R ≤ companion F R :=
  cpn.base (F := F) (R := R)

theorem companion_compat (F : MonoRel α) : Compatible F (companion F) :=
  cpn.compat

theorem companion_idem (F : MonoRel α) (R : Rel α) :
    companion F (companion F R) ≤ companion F R :=
  cpn.cpn_cpn (F := F) (R := R)

theorem companion_greatest (F : MonoRel α) {clo : Rel α → Rel α} {R : Rel α}
    (h_mono : CloMono clo) (h_compat : Compatible F clo) :
    clo R ≤ companion F R :=
  cpn.greatest (F := F) (R := R) h_mono h_compat

theorem companion_gupaco (F : MonoRel α) (R : Rel α) :
    gupaco_clo F (companion F) R ≤ companion F R := by
  simpa [companion] using cpn.gupaco (F := F) (R := R)

theorem companion_gupaco_eq (F : MonoRel α) (R : Rel α) :
    gupaco_clo F (companion F) R = companion F R := by
  simpa [companion] using cpn.gupaco_eq (F := F) (R := R)

end Paco
