import Paco.UpTo.Rclo

/-!
# Tagged Relations for Respectfulness
-/

namespace Paco

variable {α : Type*}

/-!
## Weak Respectfulness

### Proof-Relevant Tagged Relations

The Coq proof of `wrespect_compatible'` works because Coq's proof terms constructively
track which branch of a disjunction each element came from. In Lean's classical setting,
case analysis on `Or` loses this information.

To recover this, we define **tagged relations** that explicitly track provenance:
- Elements are tagged as either "unguarded" (from the base relation) or "guarded" (from F)
- This tracking is preserved through closure operations
- When we need to apply WRespectful, we can use the tag to satisfy the conditions
-/

/-- A tagged element of a relation, tracking whether it came from the "unguarded" (left)
    or "guarded" (right/F) branch. This is the proof-relevant version of `R ⊔ F R`. -/
inductive Tagged (R : Rel α) (S : Rel α) : Rel α
  | unguarded : R x y → Tagged R S x y
  | guarded : S x y → Tagged R S x y

/-- Tagged relation embeds into the union -/
theorem Tagged.toSup {R S : Rel α} : Tagged R S ≤ R ⊔ S := by
  intro x y h
  cases h with
  | unguarded hr => left; exact hr
  | guarded hs => right; exact hs

/-- Union embeds into tagged relation (non-constructively) -/
theorem Tagged.fromSup {R S : Rel α} : R ⊔ S ≤ Tagged R S := by
  intro x y h
  cases h with
  | inl hr => exact Tagged.unguarded hr
  | inr hs => exact Tagged.guarded hs

/-- Tagged is monotone in both arguments -/
theorem Tagged.mono {R R' S S' : Rel α} (hR : R ≤ R') (hS : S ≤ S') :
    Tagged R S ≤ Tagged R' S' := by
  intro x y h
  cases h with
  | unguarded hr => exact Tagged.unguarded (hR x y hr)
  | guarded hs => exact Tagged.guarded (hS x y hs)

/-- rclo with explicit guardedness tracking.

This is the key construction for the proof. Each element tracks whether it was derived
through an F application (guarded) or purely through R and clo (unguarded).

The key invariant is:
- Unguarded elements satisfy `rclo clo R`
- Guarded elements satisfy `F (rclo clo R)` -/
inductive rcloTagged (clo : Rel α → Rel α) (F : MonoRel α) (R : Rel α) : Bool → Rel α
  /-- Base unguarded: element from R -/
  | base_unguarded : R x y → rcloTagged clo F R false x y
  /-- Base guarded: element from F R -/
  | base_guarded : F R x y → rcloTagged clo F R true x y
  /-- Closure preserves guardedness tag -/
  | clo_step (b : Bool) (R' : Rel α) :
      (∀ a c, R' a c → rcloTagged clo F R b a c) →
      clo R' x y →
      rcloTagged clo F R b x y

/-- Unguarded elements of rcloTagged are in rclo clo R -/
theorem rcloTagged_unguarded_le_rclo (clo : Rel α → Rel α) (F : MonoRel α) (R : Rel α) :
    rcloTagged clo F R false ≤ rclo clo R := by
  intro x y h
  -- Generalize false to b with hypothesis hb : b = false
  generalize hb : false = b at h
  induction h with
  | base_unguarded hr => exact rclo.base hr
  | base_guarded hf => exact absurd hb Bool.false_ne_true
  | clo_step b' R' hR' hclo ih =>
    subst hb  -- b' = false
    -- ih : ∀ a c, R' a c → rclo clo R a c (the IH is over R' elements)
    have hR'_le : R' ≤ rclo clo R := fun a c hac => ih a c hac rfl
    exact rclo.clo R' hR'_le hclo

end Paco
