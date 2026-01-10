import Mathlib.Order.CompleteLattice.Basic

/-!
# Companion Equality Problem: cpn F = cpn (extendedGen F)

## Background

In parametrized coinduction (paco), the "companion" is the greatest compatible
closure operator. Given a monotone relation transformer F, we define:

- `cpn F R` = union of all F-compatible closures applied to R
- `extendedGen F` = the "relaxed" generator: `extendedGen F R = R ⊔ F R`

The Coq paco library proves that `cpn F = cpn (extendedGen F)`, meaning the
companion for F equals the companion for the extended generator.

## The Problem

We can easily show: `cpn F R ≤ cpn (extendedGen F) R`
(because F-compatible implies extendedGen-compatible)

The hard direction is: `cpn (extendedGen F) R ≤ cpn F R`

### Current Approach (Stuck)

The standard approach is:
1. Show `cpn (extendedGen F)` is F-compatible
2. By `cpn.greatest`: any F-compatible closure ≤ cpn F
3. Therefore `cpn (extendedGen F) ≤ cpn F`

Step 1 requires proving: `cpn ext (F R) ≤ F (cpn ext R)`

This proof gets stuck because ext-compatible closures don't preserve
"F-guardedness" - when we case-analyze `clo R ⊔ F (clo R)`, we lose the
information that the input was F-guarded.

### What We Need

Find a DIRECT proof that `cpn (extendedGen F) R ≤ cpn F R` without going
through F-compatibility of `cpn (extendedGen F)`.

Possible strategies:
1. Show every ext-compatible closure is "dominated by" cpn F
2. Find a common characterization of both companions
3. Use fixed-point theory to show they're the same
4. Show ext-compatible closures can be "factored" through F-compatible ones

## Goal

Prove the theorem `cpn_ext_le_cpn` below. All necessary definitions are
provided. The proof should NOT use `cpn_ext_F_compat` (which is the stuck lemma).

-/

universe u

namespace CpnEquality

variable {α : Type u}

/-!
## Core Definitions
-/

/-- Binary relation on α -/
abbrev Rel (α : Type u) := α → α → Prop

namespace Rel

/-- The bottom (empty) relation -/
def bot : Rel α := fun _ _ => False

/-- The top (full) relation -/
def top : Rel α := fun _ _ => True

/-- Union of relations -/
def union (R S : Rel α) : Rel α := fun x y => R x y ∨ S x y

/-- Intersection of relations -/
def inter (R S : Rel α) : Rel α := fun x y => R x y ∧ S x y

/-- Subset ordering on relations -/
def le (R S : Rel α) : Prop := ∀ x y, R x y → S x y

instance : Bot (Rel α) := ⟨bot⟩
instance : Top (Rel α) := ⟨top⟩
instance : Max (Rel α) := ⟨union⟩
instance : Min (Rel α) := ⟨inter⟩
instance : LE (Rel α) := ⟨le⟩
instance : LT (Rel α) := ⟨fun R S => R ≤ S ∧ ¬S ≤ R⟩

@[simp] theorem bot_apply (x y : α) : (⊥ : Rel α) x y ↔ False := Iff.rfl
@[simp] theorem top_apply (x y : α) : (⊤ : Rel α) x y ↔ True := Iff.rfl
@[simp] theorem union_apply (R S : Rel α) (x y : α) : (R ⊔ S) x y ↔ R x y ∨ S x y := Iff.rfl
@[simp] theorem inter_apply (R S : Rel α) (x y : α) : (R ⊓ S) x y ↔ R x y ∧ S x y := Iff.rfl

theorem le_def (R S : Rel α) : R ≤ S ↔ ∀ x y, R x y → S x y := Iff.rfl

theorem le_refl (R : Rel α) : R ≤ R := fun _ _ h => h

theorem le_trans {R S T : Rel α} (hRS : R ≤ S) (hST : S ≤ T) : R ≤ T :=
  fun x y hR => hST x y (hRS x y hR)

theorem le_antisymm {R S : Rel α} (hRS : R ≤ S) (hSR : S ≤ R) : R = S :=
  funext fun x => funext fun y => propext ⟨hRS x y, hSR x y⟩

/-- Supremum of a set of relations -/
protected def sSup (S : Set (Rel α)) : Rel α := fun x y => ∃ R ∈ S, R x y

/-- Infimum of a set of relations -/
protected def sInf (S : Set (Rel α)) : Rel α := fun x y => ∀ R ∈ S, R x y

instance : SupSet (Rel α) := ⟨Rel.sSup⟩
instance : InfSet (Rel α) := ⟨Rel.sInf⟩

/-- Relations form a complete lattice -/
instance instCompleteLattice : CompleteLattice (Rel α) where
  sup := union
  le := le
  lt := fun R S => R ≤ S ∧ ¬S ≤ R
  le_refl := le_refl
  le_trans := fun _ _ _ => le_trans
  le_antisymm := fun _ _ => le_antisymm
  le_sup_left := fun R S x y hR => Or.inl hR
  le_sup_right := fun R S x y hS => Or.inr hS
  sup_le := fun R S T hRT hST x y h => h.elim (hRT x y) (hST x y)
  inf := inter
  inf_le_left := fun R S x y ⟨hR, _⟩ => hR
  inf_le_right := fun R S x y ⟨_, hS⟩ => hS
  le_inf := fun R S T hRS hRT x y hR => ⟨hRS x y hR, hRT x y hR⟩
  sSup := Rel.sSup
  le_sSup := fun S R hR x y hRxy => ⟨R, hR, hRxy⟩
  sSup_le := fun S R hSR x y ⟨T, hT, hTxy⟩ => hSR T hT x y hTxy
  sInf := Rel.sInf
  sInf_le := fun S R hR x y hxy => hxy R hR
  le_sInf := fun S R hRS x y hRxy T hT => hRS T hT x y hRxy
  top := top
  bot := bot
  le_top := fun _ _ _ _ => trivial
  bot_le := fun _ _ _ h => h.elim

end Rel

/-- Bundled monotone relation transformer -/
structure MonoRel (α : Type u) where
  F : Rel α → Rel α
  mono : ∀ R S, R ≤ S → F R ≤ F S

/-- Convenience for applying monotonicity -/
theorem MonoRel.mono' {F : MonoRel α} {R S : Rel α} (h : R ≤ S) : F.F R ≤ F.F S :=
  F.mono R S h

/-- A closure operator is monotone -/
def CloMono (clo : Rel α → Rel α) : Prop :=
  ∀ R S, R ≤ S → clo R ≤ clo S

/-- Strong compatibility: clo (F R) ≤ F (clo R) -/
def Compatible (F : MonoRel α) (clo : Rel α → Rel α) : Prop :=
  ∀ R, clo (F.F R) ≤ F.F (clo R)

/-- The extended generator: extendedGen F R = R ⊔ F R -/
def extendedGen (F : MonoRel α) : MonoRel α where
  F := fun R => R ⊔ F.F R
  mono := fun _ _ hRS => sup_le_sup hRS (F.mono' hRS)

/-!
## The Companion (cpn)

The companion is defined as the union of all compatible monotone closures.
-/

/-- The companion: greatest compatible closure operator -/
inductive cpn (F : MonoRel α) (R : Rel α) : Rel α where
  | intro (clo : Rel α → Rel α) (h_mono : CloMono clo) (h_compat : Compatible F clo)
          (h_clo : clo R x y) : cpn F R x y

namespace cpn

variable {F : MonoRel α} {R S : Rel α}

/-- cpn is monotone -/
theorem mono : R ≤ S → cpn F R ≤ cpn F S := fun hRS x y ⟨clo, h_mono, h_compat, h_clo⟩ =>
  ⟨clo, h_mono, h_compat, h_mono R S hRS x y h_clo⟩

/-- cpn F is a monotone closure operator -/
theorem cpn_cloMono : CloMono (cpn F) := fun _ _ h => mono h

/-- Any compatible monotone closure is contained in cpn -/
theorem greatest {clo : Rel α → Rel α} (h_mono : CloMono clo) (h_compat : Compatible F clo) :
    clo R ≤ cpn F R := fun _ _ h => ⟨clo, h_mono, h_compat, h⟩

/-- R is contained in cpn F R (via identity closure) -/
theorem base : R ≤ cpn F R :=
  greatest (fun _ _ h => h) (fun _ => Rel.le_refl _)

/-- cpn F is compatible with F -/
theorem compat : Compatible F (cpn F) := fun R x y ⟨clo, h_mono, h_compat, h_clo⟩ =>
  let h1 : clo (F.F R) ≤ F.F (clo R) := h_compat R
  let h2 : clo R ≤ cpn F R := greatest h_mono h_compat
  let h3 : F.F (clo R) ≤ F.F (cpn F R) := F.mono' h2
  h3 x y (h1 x y h_clo)

/-- cpn is idempotent -/
theorem cpn_cpn : cpn F (cpn F R) ≤ cpn F R := by
  intro x y ⟨clo, h_mono, h_compat, h_clo⟩
  have h_comp_mono : CloMono (clo ∘ cpn F) := fun R S hRS =>
    h_mono (cpn F R) (cpn F S) (cpn_cloMono R S hRS)
  have h_comp_compat : Compatible F (clo ∘ cpn F) := by
    intro R' x' y' hclo
    have h1 : clo (cpn F (F.F R')) ≤ clo (F.F (cpn F R')) := h_mono _ _ (compat R')
    have h2 : clo (F.F (cpn F R')) ≤ F.F (clo (cpn F R')) := h_compat (cpn F R')
    exact h2 x' y' (h1 x' y' hclo)
  have h_le : (clo ∘ cpn F) R ≤ cpn F R := greatest h_comp_mono h_comp_compat
  exact h_le x y h_clo

/-- F (cpn F R) ≤ cpn F R (F-application is absorbed) -/
theorem step : F.F (cpn F R) ≤ cpn F R :=
  let clo : Rel α → Rel α := fun X => F.F (cpn F X)
  let h_mono : CloMono clo := fun R S hRS => F.mono' (cpn_cloMono R S hRS)
  let h_compat : Compatible F clo := fun R' x y hclo =>
    let h_cpn_compat : cpn F (F.F R') ≤ F.F (cpn F R') := compat R'
    F.mono' h_cpn_compat x y hclo
  greatest h_mono h_compat

end cpn

/-!
## Easy Direction: cpn F ≤ cpn ext

F-compatible implies ext-compatible (under mild conditions).
-/

/-- Identity is compatible with any F -/
theorem compatible_id (F : MonoRel α) : Compatible F id := fun _ => Rel.le_refl _

/-- F-compatibility implies extendedGen-compatibility for sub-additive closures -/
theorem F_compat_imp_ext_compat {F : MonoRel α} {clo : Rel α → Rel α}
    (_h_mono : CloMono clo)
    (h_compat : Compatible F clo)
    (h_subadd : ∀ R S, clo (R ⊔ S) ≤ clo R ⊔ clo S) :
    Compatible (extendedGen F) clo := fun R x y hclo =>
  -- clo (R ⊔ F R) ≤ clo R ⊔ clo (F R) ≤ clo R ⊔ F (clo R)
  let h1 : clo (R ⊔ F.F R) ≤ clo R ⊔ clo (F.F R) := h_subadd R (F.F R)
  let h2 : clo (F.F R) ≤ F.F (clo R) := h_compat R
  match h1 x y hclo with
  | Or.inl h => Or.inl h
  | Or.inr h => Or.inr (h2 x y h)

/-- cpn F is ext-compatible (assuming cpn F is sub-additive) -/
theorem cpn_ext_compat_if_subadd (F : MonoRel α)
    (h_subadd : ∀ R S, cpn F (R ⊔ S) ≤ cpn F R ⊔ cpn F S) :
    Compatible (extendedGen F) (cpn F) :=
  F_compat_imp_ext_compat cpn.cpn_cloMono cpn.compat h_subadd

/-- cpn F ≤ cpn ext (the easy direction, assuming sub-additivity) -/
theorem cpn_le_cpn_ext_if_subadd (F : MonoRel α) (R : Rel α)
    (h_subadd : ∀ R S, cpn F (R ⊔ S) ≤ cpn F R ⊔ cpn F S) :
    cpn F R ≤ cpn (extendedGen F) R :=
  cpn.greatest cpn.cpn_cloMono (cpn_ext_compat_if_subadd F h_subadd)

/-!
## The Hard Direction: cpn ext ≤ cpn F

This is what we need to prove WITHOUT using F-compatibility of cpn ext.
-/

/-- STUCK LEMMA: cpn ext is F-compatible.
    This is the traditional approach but the proof gets stuck. DO NOT USE. -/
theorem cpn_ext_F_compat (F : MonoRel α) : Compatible F (cpn (extendedGen F)) := fun R x y hcpn =>
  -- This proof is stuck! See the problem description above.
  sorry

/-- ========== THE KEY THEOREM TO PROVE ==========

    Show that cpn (extendedGen F) R ≤ cpn F R directly,
    WITHOUT going through cpn_ext_F_compat.

    Strategy hints:
    1. Every element of cpn ext R comes from some ext-compatible clo with clo R x y
    2. Need to show that element is also in cpn F R
    3. This means finding an F-compatible clo' with clo' R x y

    Possible approaches:
    - Show ext-compatible closures can be "converted" to F-compatible ones
    - Use fixed-point characterization of cpn
    - Show cpn F R already contains all ext-compatible closures applied to R
    - Use the absorption property: F (cpn F R) ≤ cpn F R

    Key facts available:
    - cpn.step: F (cpn F R) ≤ cpn F R
    - cpn.compat: cpn F (F R) ≤ F (cpn F R)
    - cpn.cpn_cpn: cpn F (cpn F R) ≤ cpn F R
-/
theorem cpn_ext_le_cpn (F : MonoRel α) (R : Rel α) :
    cpn (extendedGen F) R ≤ cpn F R := by
  sorry

/-- The main equality: cpn F = cpn ext -/
theorem cpn_eq_cpn_ext (F : MonoRel α) (R : Rel α)
    (h_subadd : ∀ R S, cpn F (R ⊔ S) ≤ cpn F R ⊔ cpn F S) :
    cpn F R = cpn (extendedGen F) R := by
  apply Rel.le_antisymm
  · exact cpn_le_cpn_ext_if_subadd F R h_subadd
  · exact cpn_ext_le_cpn F R

end CpnEquality
