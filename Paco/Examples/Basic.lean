import Paco.Basic

/-!
# Paco Example: Minimal Template

This file is a tiny, self-contained template for using paco.
It shows how to define a monotone relation transformer and prove
coinductive facts with `paco_coind` and `paco_unfold`.
-/

namespace Paco.Examples

open Paco

variable {α : Type}

/-- A simple relation transformer: relate elements if they are equal. -/
def EqF : MonoRel α :=
  ⟨fun R x y => x = y ∨ R x y, by
    intro R S hRS x y hxy
    cases hxy with
    | inl heq => exact Or.inl heq
    | inr hR => exact Or.inr (hRS x y hR)
  ⟩

/-- `paco EqF ⊥` contains equality (by coinduction). -/
theorem paco_eq (x : α) : paco EqF ⊥ x x := by
  apply paco_coind EqF (fun a b => a = b) ⊥
  · intro a b hab
    subst hab
    simp only [Rel.sup_bot]
    exact Or.inl rfl
  · rfl

/-- Unfolding a paco hypothesis yields an `EqF` step. -/
example (x y : α) (h : paco EqF ⊥ x y) : EqF (upaco EqF ⊥) x y := by
  simpa using (paco_unfold EqF ⊥ x y h)

end Paco.Examples
