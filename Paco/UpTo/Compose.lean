import Paco.UpTo.Compat
import Paco.UpTo.Closures

/-!
# Closure Composition Lemmas

Systematic composition results for common closures.
This module provides lemmas about how closures interact when composed.
-/

namespace Paco

variable {α : Type*}

/-!
## Composition Monotonicity
-/

/-- Composition of monotone closures is monotone -/
theorem cloMono_comp {clo₁ clo₂ : Rel α → Rel α}
    (h₁ : CloMono clo₁) (h₂ : CloMono clo₂) :
    CloMono (clo₁ ∘ clo₂) := by
  intro R S hRS
  exact h₁ _ _ (h₂ _ _ hRS)

/-!
## Closure Idempotence

Many closures satisfy `clo (clo R) = clo R`.
-/

/-- reflClosure is idempotent -/
theorem reflClosure_idem (R : Rel α) :
    reflClosure (reflClosure R) = reflClosure R := by
  ext x y
  constructor
  · intro h
    cases h with
    | inl heq => left; exact heq
    | inr hinner =>
      cases hinner with
      | inl heq' => left; exact heq'
      | inr hR => right; exact hR
  · intro h
    right; exact h

/-- symmClosure is idempotent -/
theorem symmClosure_idem (R : Rel α) :
    symmClosure (symmClosure R) = symmClosure R := by
  ext x y
  constructor
  · intro h
    cases h with
    | inl hs => exact hs
    | inr hs =>
      cases hs with
      | inl hr => right; exact hr
      | inr hr => left; exact hr
  · intro h
    left; exact h

/-- transClosure is idempotent -/
theorem transClosure_idem (R : Rel α) :
    transClosure (transClosure R) = transClosure R := by
  ext x y
  constructor
  · intro h
    induction h with
    | base hinner => exact hinner
    | trans _ _ ih₁ ih₂ => exact transClosure.trans ih₁ ih₂
  · intro h
    exact transClosure.base h

/-- rtClosure is idempotent -/
theorem rtClosure_idem (R : Rel α) :
    rtClosure (rtClosure R) = rtClosure R := by
  ext x y
  constructor
  · intro h
    induction h with
    | refl => exact rtClosure.refl
    | base hinner => exact hinner
    | trans _ _ ih₁ ih₂ => exact rtClosure.trans ih₁ ih₂
  · intro h
    exact rtClosure.base h

/-- eqvClosure is idempotent -/
theorem eqvClosure_idem (R : Rel α) :
    eqvClosure (eqvClosure R) = eqvClosure R := by
  ext x y
  constructor
  · intro h
    induction h with
    | refl => exact eqvClosure.refl
    | base hinner => exact hinner
    | symm _ ih => exact eqvClosure.symm ih
    | trans _ _ ih₁ ih₂ => exact eqvClosure.trans ih₁ ih₂
  · intro h
    exact eqvClosure.base h

/-!
## Closure Absorption

When one closure subsumes another.
-/

/-- rtClosure absorbs reflClosure -/
theorem rtClosure_reflClosure (R : Rel α) :
    rtClosure (reflClosure R) = rtClosure R := by
  ext x y
  constructor
  · intro h
    induction h with
    | refl => exact rtClosure.refl
    | base hrefl =>
      cases hrefl with
      | inl heq => subst heq; exact rtClosure.refl
      | inr hR => exact rtClosure.base hR
    | trans _ _ ih₁ ih₂ => exact rtClosure.trans ih₁ ih₂
  · intro h
    induction h with
    | refl => exact rtClosure.refl
    | base hR => exact rtClosure.base (Or.inr hR)
    | trans _ _ ih₁ ih₂ => exact rtClosure.trans ih₁ ih₂

/-- rtClosure absorbs transClosure -/
theorem rtClosure_transClosure (R : Rel α) :
    rtClosure (transClosure R) = rtClosure R := by
  ext x y
  constructor
  · intro h
    induction h with
    | refl => exact rtClosure.refl
    | base htrans =>
      induction htrans with
      | base hR => exact rtClosure.base hR
      | trans _ _ ih₁ ih₂ => exact rtClosure.trans ih₁ ih₂
    | trans _ _ ih₁ ih₂ => exact rtClosure.trans ih₁ ih₂
  · intro h
    induction h with
    | refl => exact rtClosure.refl
    | base hR => exact rtClosure.base (transClosure.base hR)
    | trans _ _ ih₁ ih₂ => exact rtClosure.trans ih₁ ih₂

/-- eqvClosure absorbs reflClosure -/
theorem eqvClosure_reflClosure (R : Rel α) :
    eqvClosure (reflClosure R) = eqvClosure R := by
  ext x y
  constructor
  · intro h
    induction h with
    | refl => exact eqvClosure.refl
    | base hrefl =>
      cases hrefl with
      | inl heq => subst heq; exact eqvClosure.refl
      | inr hR => exact eqvClosure.base hR
    | symm _ ih => exact eqvClosure.symm ih
    | trans _ _ ih₁ ih₂ => exact eqvClosure.trans ih₁ ih₂
  · intro h
    induction h with
    | refl => exact eqvClosure.refl
    | base hR => exact eqvClosure.base (Or.inr hR)
    | symm _ ih => exact eqvClosure.symm ih
    | trans _ _ ih₁ ih₂ => exact eqvClosure.trans ih₁ ih₂

/-- eqvClosure absorbs symmClosure -/
theorem eqvClosure_symmClosure (R : Rel α) :
    eqvClosure (symmClosure R) = eqvClosure R := by
  ext x y
  constructor
  · intro h
    induction h with
    | refl => exact eqvClosure.refl
    | base hsymm =>
      cases hsymm with
      | inl hR => exact eqvClosure.base hR
      | inr hR => exact eqvClosure.symm (eqvClosure.base hR)
    | symm _ ih => exact eqvClosure.symm ih
    | trans _ _ ih₁ ih₂ => exact eqvClosure.trans ih₁ ih₂
  · intro h
    induction h with
    | refl => exact eqvClosure.refl
    | base hR => exact eqvClosure.base (Or.inl hR)
    | symm _ ih => exact eqvClosure.symm ih
    | trans _ _ ih₁ ih₂ => exact eqvClosure.trans ih₁ ih₂

/-!
## Closure Containment
-/

/-- R is contained in reflClosure R -/
theorem le_reflClosure (R : Rel α) : R ≤ reflClosure R :=
  fun _ _ h => Or.inr h

/-- R is contained in symmClosure R -/
theorem le_symmClosure (R : Rel α) : R ≤ symmClosure R :=
  fun _ _ h => Or.inl h

/-- R is contained in transClosure R -/
theorem le_transClosure (R : Rel α) : R ≤ transClosure R :=
  fun _ _ h => transClosure.base h

/-- R is contained in rtClosure R -/
theorem le_rtClosure (R : Rel α) : R ≤ rtClosure R :=
  fun _ _ h => rtClosure.base h

/-- R is contained in eqvClosure R -/
theorem le_eqvClosure (R : Rel α) : R ≤ eqvClosure R :=
  fun _ _ h => eqvClosure.base h

/-!
## Convenience re-exports

Compatibility composition (re-export from Compat.lean for convenience)
-/

/-- If clo₁ and clo₂ are both compatible with F, and clo₁ is monotone,
    then clo₁ ∘ clo₂ is compatible with F. -/
theorem compatible_compose (F : MonoRel α) {clo₁ clo₂ : Rel α → Rel α}
    (h₁_mono : CloMono clo₁) (h₁ : Compatible F clo₁) (h₂ : Compatible F clo₂) :
    Compatible F (clo₁ ∘ clo₂) :=
  compatible_comp F h₁_mono h₁ h₂

/-!
## Identity simplifications
-/

@[simp] theorem id_comp_clo (clo : Rel α → Rel α) : id ∘ clo = clo := rfl

@[simp] theorem clo_comp_id (clo : Rel α → Rel α) : clo ∘ id = clo := rfl

/-!
## Conditional Compatibility Helpers

Wrappers that give clearer names to the conditional compatibility theorems.
-/

/-- reflClosure is compatible when F preserves reflexivity -/
theorem reflClosure_compat_of_refl (F : MonoRel α)
    (hF : ∀ R, (∀ x, R x x) → ∀ x, F R x x) :
    Compatible F reflClosure :=
  reflClosure_compatible F hF

/-- symmClosure is compatible when F commutes with symmetry -/
theorem symmClosure_compat_of_symm (F : MonoRel α)
    (hF : ∀ R x y, F R x y → F (symmClosure R) y x) :
    Compatible F symmClosure :=
  symmClosure_compatible F hF

/-- congClosure is compatible when F respects the function -/
theorem congClosure_compat_of_cong (F : MonoRel α) (f : α → α)
    (hF : ∀ R x y, F R x y → F (congClosure f R) (f x) (f y)) :
    Compatible F (congClosure f) :=
  congClosure_compatible F f hF

end Paco
