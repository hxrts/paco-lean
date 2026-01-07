import Paco.Basic
import Qpf.ITree.Bisim

/-!
# Integration: ITree Bisimulation via Paco

This module demonstrates how to use parametrized coinduction (paco) for
ITree bisimulation proofs. We show that:

1. `Bisim.F` is monotone (making it suitable for paco)
2. `Bisim` equals `paco Bisim.monoRel ⊥` (the paco formulation)
3. Bisim properties can be derived from paco lemmas

## Key Results

- `Bisim.F_mono`: Monotonicity of the bisimulation functor
- `Bisim.monoRel`: Bundled monotone relation transformer
- `Bisim_eq_paco`: Equivalence between Bisim and paco formulation
- `Bisim.trans_paco`: Transitivity proof using paco accumulation

## References

- [Paco: Parameterized Coinduction (POPL 2013)](https://plv.mpi-sws.org/paco/)
- [Interaction Trees (POPL 2020)](https://arxiv.org/abs/1906.00046)
-/

namespace ITree

open Paco

/-!
## Bisim.F is Monotone
-/

/-- The bisimulation functor `Bisim.F` is monotone in the relation parameter.

If `R ≤ S` (i.e., `R` implies `S` pointwise), then `Bisim.F R ≤ Bisim.F S`. -/
theorem Bisim.F_mono {α ε ρ : Type} : Monotone2 (Bisim.F (α := α) (ε := ε) (ρ := ρ)) := by
  intro R S hRS x y ⟨hterm, hvis_lr, hvis_rl⟩
  constructor
  · -- Termination: unchanged (doesn't depend on R)
    exact hterm
  constructor
  · -- CanDo left-to-right: lift continuations from R to S
    intro e k₁ hk₁
    obtain ⟨k₂, hk₂, hcont⟩ := hvis_lr e k₁ hk₁
    exact ⟨k₂, hk₂, fun a => hRS _ _ (hcont a)⟩
  · -- CanDo right-to-left: lift continuations from R to S
    intro e k₂ hk₂
    obtain ⟨k₁, hk₁, hcont⟩ := hvis_rl e k₂ hk₂
    exact ⟨k₁, hk₁, fun a => hRS _ _ (hcont a)⟩

/-- `Bisim.F` as a bundled monotone relation transformer.

This allows using `Bisim.F` with all paco lemmas. -/
def Bisim.monoRel (α ε ρ : Type) : MonoRel (ITree α ε ρ) :=
  ⟨Bisim.F, Bisim.F_mono⟩

/-!
## Bisim Equals Paco

We show that the coinductive definition of `Bisim` is equivalent to
`paco Bisim.monoRel ⊥`.
-/

/-- `Bisim` is exactly `paco Bisim.monoRel ⊥`.

This establishes that the direct coinductive definition matches the
parametrized coinduction formulation. -/
theorem Bisim_eq_paco {α ε ρ : Type} :
    Bisim (α := α) (ε := ε) (ρ := ρ) = paco (Bisim.monoRel α ε ρ) ⊥ := by
  ext x y
  constructor
  · -- Bisim x y → paco Bisim.monoRel ⊥ x y
    intro ⟨R, hR, hxy⟩
    refine ⟨R, ?_, hxy⟩
    intro a b hab
    simp only [Rel.sup_bot]
    exact hR a b hab
  · -- paco Bisim.monoRel ⊥ x y → Bisim x y
    intro ⟨R, hR, hxy⟩
    refine ⟨R, ?_, hxy⟩
    intro a b hab
    simp only [Rel.sup_bot] at hR
    exact hR a b hab

/-!
## Bisim Properties via Paco

We can derive bisimulation properties from the corresponding paco lemmas.
-/

/-- Bisim is reflexive (derived from paco). -/
theorem Bisim.refl_paco (t : ITree α ε ρ) : Bisim t t := by
  rw [Bisim_eq_paco]
  apply paco_coind (Bisim.monoRel α ε ρ) (fun a b => a = b) ⊥
  · intro a b hab
    subst hab
    simp only [Rel.sup_bot]
    exact ⟨fun _ => Iff.rfl,
           fun e k h => ⟨k, h, fun _ => rfl⟩,
           fun e k h => ⟨k, h, fun _ => rfl⟩⟩
  · rfl

/-- Bisim is symmetric (derived from paco). -/
theorem Bisim.symm_paco {t₁ t₂ : ITree α ε ρ} : Bisim t₁ t₂ → Bisim t₂ t₁ := by
  rw [Bisim_eq_paco]
  intro ⟨R, hR, hxy⟩
  refine ⟨flip R, ?_, hxy⟩
  intro a b hab
  simp only [Rel.sup_bot] at hR ⊢
  obtain ⟨hterm, hvis₁, hvis₂⟩ := hR b a hab
  exact ⟨fun r => (hterm r).symm, hvis₂, hvis₁⟩

/-- Transitivity via paco accumulation.

This proof demonstrates the power of paco: instead of manually constructing
the composition relation, we use `paco_coind` with the natural witness
`R a c := ∃ b, paco F ⊥ a b ∧ paco F ⊥ b c`. -/
theorem Bisim.trans_paco {t₁ t₂ t₃ : ITree α ε ρ} :
    Bisim t₁ t₂ → Bisim t₂ t₃ → Bisim t₁ t₃ := by
  rw [Bisim_eq_paco]
  intro hxy hyz
  -- Define the composition relation as our witness
  let R : Rel (ITree α ε ρ) := fun a c =>
    ∃ b, paco (Bisim.monoRel α ε ρ) ⊥ a b ∧ paco (Bisim.monoRel α ε ρ) ⊥ b c
  apply paco_coind (Bisim.monoRel α ε ρ) R ⊥
  · -- Show R is a post-fixpoint of Bisim.F
    intro a c ⟨b, hab, hbc⟩
    simp only [Rel.sup_bot]
    -- Unfold both paco hypotheses to get Bisim.F structure
    have hab' := paco_unfold (Bisim.monoRel α ε ρ) ⊥ a b hab
    have hbc' := paco_unfold (Bisim.monoRel α ε ρ) ⊥ b c hbc
    simp only [upaco, Rel.sup_bot] at hab' hbc'
    -- hab' : Bisim.F (paco ...) a b
    -- hbc' : Bisim.F (paco ...) b c
    obtain ⟨hterm_ab, hvis_ab_lr, hvis_ab_rl⟩ := hab'
    obtain ⟨hterm_bc, hvis_bc_lr, hvis_bc_rl⟩ := hbc'
    constructor
    · -- Termination: transitivity of ↔
      intro r
      exact (hterm_ab r).trans (hterm_bc r)
    constructor
    · -- CanDo left-to-right: chain through b
      intro e k₁ hk₁
      obtain ⟨k₂, hk₂, hcont₁⟩ := hvis_ab_lr e k₁ hk₁
      obtain ⟨k₃, hk₃, hcont₂⟩ := hvis_bc_lr e k₂ hk₂
      refine ⟨k₃, hk₃, fun a => ?_⟩
      -- Need: (R ⊔ ⊥) (k₁ a) (k₃ a), i.e., R (k₁ a) (k₃ a)
      exact ⟨k₂ a, hcont₁ a, hcont₂ a⟩
    · -- CanDo right-to-left: chain through b
      intro e k₃ hk₃
      obtain ⟨k₂, hk₂, hcont₂⟩ := hvis_bc_rl e k₃ hk₃
      obtain ⟨k₁, hk₁, hcont₁⟩ := hvis_ab_rl e k₂ hk₂
      refine ⟨k₁, hk₁, fun a => ?_⟩
      exact ⟨k₂ a, hcont₁ a, hcont₂ a⟩
  · -- Show R t₁ t₃
    exact ⟨t₂, hxy, hyz⟩

/-!
## Alternative: Using Paco Accumulation Directly

The `paco_acc` lemma allows accumulating facts during proofs. Here we show
how it can simplify certain proof patterns.
-/

/-- Unfold a Bisim to get Bisim.F structure (via paco_unfold). -/
theorem Bisim.unfold {t₁ t₂ : ITree α ε ρ} (h : Bisim t₁ t₂) :
    Bisim.F (upaco (Bisim.monoRel α ε ρ) ⊥) t₁ t₂ := by
  rw [Bisim_eq_paco] at h
  exact paco_unfold (Bisim.monoRel α ε ρ) ⊥ t₁ t₂ h

/-- Fold Bisim.F back into Bisim (via paco_fold). -/
theorem Bisim.fold {t₁ t₂ : ITree α ε ρ}
    (h : Bisim.F (upaco (Bisim.monoRel α ε ρ) ⊥) t₁ t₂) : Bisim t₁ t₂ := by
  rw [Bisim_eq_paco]
  exact paco_fold (Bisim.monoRel α ε ρ) ⊥ t₁ t₂ h

/-- Bisim with paco accumulation: we can accumulate Bisim facts in the parameter.

This follows from `paco_acc`: `paco F (paco F r) ≤ paco F r`. -/
theorem Bisim.acc {t₁ t₂ : ITree α ε ρ} :
    paco (Bisim.monoRel α ε ρ) (paco (Bisim.monoRel α ε ρ) ⊥) t₁ t₂ →
    Bisim t₁ t₂ := by
  rw [Bisim_eq_paco]
  exact paco_acc (Bisim.monoRel α ε ρ) ⊥ t₁ t₂

end ITree
