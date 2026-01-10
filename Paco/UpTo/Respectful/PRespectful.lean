import Paco.UpTo.Respectful.Core

/-!
# Paco Respectfulness
-/

namespace Paco

variable {α : Type*}

structure PRespectful (F : MonoRel α) (clo : Rel α → Rel α) : Prop where
  /-- The closure is monotone -/
  mon : CloMono clo
  /-- The respect condition: clo l ≤ paco F (r ⊔ clo r) when l ≤ r and l ≤ F r -/
  respect : ∀ l r, l ≤ r → l ≤ F r → clo l ≤ paco F (r ⊔ clo r)

/-- The closure operator for PRespectful: R ↦ upaco F (R ⊔ clo R).

This is the key closure used in proving PRespectful implies ≤ companion.
By showing this closure is compatible', we can use compatible'_le_companion. -/
def prespectClosure (F : MonoRel α) (clo : Rel α → Rel α) : Rel α → Rel α :=
  fun R => upaco F (R ⊔ clo R)

/-- prespectClosure is monotone when clo is monotone -/
theorem prespectClosure_mono (F : MonoRel α) {clo : Rel α → Rel α}
    (h_mono : CloMono clo) : CloMono (prespectClosure F clo) := by
  intro R S hRS x y hpre
  simp only [prespectClosure] at hpre ⊢
  have h1 : R ⊔ clo R ≤ S ⊔ clo S := sup_le_sup hRS (h_mono R S hRS)
  exact upaco_mon F h1 x y hpre

/-- clo R is contained in prespectClosure -/
theorem clo_le_prespectClosure (F : MonoRel α) (clo : Rel α → Rel α) (R : Rel α) :
    clo R ≤ prespectClosure F clo R := by
  intro x y hclo
  simp only [prespectClosure, upaco]
  right  -- go to clo R side of the union
  exact Or.inr hclo

/-- Paco respectfulness implies the closure is contained in the companion.

Currently routed through the Compatible' → companion chain, which requires:
- `Compatible' F clo`
- `ExtCompatImpliesCompat F`

This keeps the lemma usable in settings where Compatible' is available. -/
theorem prespect_companion (F : MonoRel α) {clo : Rel α → Rel α}
    (h : PRespectful F clo) (h_compat' : Compatible' F clo)
    [ExtCompatImpliesCompat F] : ∀ R, clo R ≤ companion F R :=
  compatible'_le_companion F h.mon h_compat'

/-- Paco respectfulness uclo lemma: clo R ≤ gupaco_clo F (companion F) R -/
theorem prespect_uclo (F : MonoRel α) {clo : Rel α → Rel α}
    (h : PRespectful F clo) (h_compat' : Compatible' F clo)
    [ExtCompatImpliesCompat F] (R : Rel α) :
    clo R ≤ gupaco_clo F (companion F) R := by
  intro x y hclo
  have h1 : clo R ≤ companion F R := prespect_companion F h h_compat' R
  have h2 : companion F R = gupaco_clo F (companion F) R := (companion_gupaco_eq F R).symm
  rw [← h2]
  exact h1 x y hclo

end Paco
