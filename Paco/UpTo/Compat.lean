import Paco.UpTo.Rclo

/-!
# Compatibility

A closure operator `clo` is compatible with `F` if it commutes appropriately
with the generating function.
-/

namespace Paco

variable {α : Type*}

/-- Strong compatibility: clo (F R) ≤ F (clo R).

This allows using clo during coinduction without breaking the argument. -/
def Compatible (F : MonoRel α) (clo : Rel α → Rel α) : Prop :=
  ∀ R, clo (F R) ≤ F (clo R)

/-- A closure is monotone if R ≤ S implies clo R ≤ clo S -/
def CloMono (clo : Rel α → Rel α) : Prop := Monotone2 clo

/-!
## Basic Compatible Closures
-/

/-- Identity is compatible with any F -/
theorem compatible_id (F : MonoRel α) : Compatible F id := fun _ => Rel.le_refl _

/-- Identity is monotone -/
theorem cloMono_id : CloMono (id : Rel α → Rel α) := fun _ _ h => h

/-- Composition of compatible closures is compatible -/
theorem compatible_comp (F : MonoRel α) {clo₁ clo₂ : Rel α → Rel α}
    (h₁_mono : CloMono clo₁) (h₁ : Compatible F clo₁) (h₂ : Compatible F clo₂) :
    Compatible F (clo₁ ∘ clo₂) := by
  intro R
  calc clo₁ (clo₂ (F R)) ≤ clo₁ (F (clo₂ R)) := h₁_mono _ _ (h₂ R)
    _ ≤ F (clo₁ (clo₂ R)) := h₁ (clo₂ R)

/-- rclo of a compatible monotone closure is compatible -/
theorem rclo_compatible (F : MonoRel α) {clo : Rel α → Rel α}
    (h_mono : CloMono clo) (h_compat : Compatible F clo) :
    Compatible F (rclo clo) := by
  intro R x y h
  induction h with
  | base hFR => exact F.mono' rclo.base_le _ _ hFR
  | clo R' _ hcloR' ih =>
    have h1 : clo R' ≤ clo (F (rclo clo R)) := h_mono R' _ ih
    have h2 : clo (F (rclo clo R)) ≤ F (clo (rclo clo R)) := h_compat (rclo clo R)
    have h3 : clo (rclo clo R) ≤ rclo clo R := rclo.clo_rclo
    have h4 : F (clo (rclo clo R)) ≤ F (rclo clo R) := F.mono' h3
    exact h4 _ _ (h2 _ _ (h1 _ _ hcloR'))

/-- rclo of a monotone closure is monotone -/
theorem rclo_mono (clo : Rel α → Rel α) : CloMono (rclo clo) :=
  fun _ _ h => rclo.mono h

end Paco
