import Paco

/-!
# Example-Driven Validation

This file provides small, fully worked examples used as smoke tests.
-/

namespace Paco.Tests.Examples

open Paco

/-!
## Basic paco example: Equality relation
-/

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

/-!
## Stream bisimulation with an up-to closure
-/

def Stream (α : Type*) := Nat → α

def head {α : Type*} (s : Stream α) : α := s 0

def tail {α : Type*} (s : Stream α) : Stream α := fun n => s (n + 1)

/-- Stream bisimulation generator. -/
def StreamF (α : Type*) : MonoRel (Stream α) :=
  ⟨fun R s t => head s = head t ∧ R (tail s) (tail t), by
    intro R S hRS s t h
    exact And.intro h.1 (hRS _ _ h.2)
  ⟩

/-- Reflexive bisimulation using `reflClosure` with `gupaco_clo`. -/
theorem stream_bisim_refl (α : Type*) (s : Stream α) :
    gupaco_clo (StreamF α) reflClosure ⊥ s s := by
  apply upto_coind_bot (F := StreamF α) (clo := reflClosure) (R := fun a b => a = b)
  · rfl
  · intro a b hab
    subst hab
    constructor
    · rfl
    · exact rclo.base (Or.inl rfl)

/-!
## TagRoundtrip usage with a minimal instance
-/

def BotF (α : Type*) : MonoRel α :=
  ⟨fun _ _ _ => False, by
    intro R S hRS x y h
    exact False.elim h
  ⟩

def idClosure {α : Type*} (R : Rel α) : Rel α := R

lemma paco_botF {α : Type*} (r : Rel α) : paco (BotF α) r = ⊥ := by
  ext x y
  constructor
  · intro h
    rcases h with ⟨R, hpost, hxy⟩
    exact False.elim (hpost _ _ hxy)
  · intro h
    cases h

lemma prespectClosure_bot_id {α : Type*} (R : Rel α) :
    prespectClosure (BotF α) idClosure R = R := by
  simp [prespectClosure, idClosure, upaco, paco_botF]

lemma prespectful_bot_id {α : Type*} : PRespectful (BotF α) idClosure := by
  refine ⟨?_, ?_⟩
  · intro R S hRS x y h
    exact hRS _ _ h
  · intro l r hle hleF x y hclo
    exact False.elim (hleF _ _ hclo)

local instance tagRoundtrip_bot_id {α : Type*} : TagRoundtrip (BotF α) idClosure :=
  ⟨by
    intro R S x y h
    have h' : (R ⊔ S) x y := by
      simpa [prespectClosure_bot_id] using h
    have h'' : (prespectClosure (BotF α) idClosure R ⊔
        prespectClosure (BotF α) idClosure S) x y := by
      simpa [prespectClosure_bot_id] using h'
    simpa [forgetTag_prespectClosure, projLeft_taggedUnion, projRight_taggedUnion] using h''
  ⟩

local instance prespectRightGuarded_bot_id {α : Type*} : PrespectRightGuarded (BotF α) idClosure :=
  ⟨by
    intro R x y h
    exact False.elim (by
      simpa [prespectClosure_bot_id] using h)
  ⟩

/-- A concrete use of `TagRoundtrip` to obtain compatibility. -/
example (α : Type*) : Compatible' (BotF α) (prespectClosure (BotF α) idClosure) := by
  have h : PRespectful (BotF α) idClosure := prespectful_bot_id
  exact prespect_compatible'_tagged (F := BotF α) (clo := idClosure) h

end Paco.Tests.Examples
