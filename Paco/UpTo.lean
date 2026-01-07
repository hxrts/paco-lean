import Paco.Basic
import Paco.GPaco

/-!
# Up-To Techniques for Paco (GPaco with Closures)

This module provides "up-to" techniques for parametrized coinduction following
the Coq gpaco library architecture. The key insight is that gpaco composes
the generating function with a reflexive-transitive closure operator.

## Architecture

The gpaco framework extends paco by:
1. `rclo clo R`: Reflexive-transitive closure under closure operator `clo`
2. Modified generating function: `F ∘ rclo clo`
3. `gpaco_clo clo r rg = rclo clo (paco (F ∘ rclo clo) (rg ⊔ r) ⊔ r)`
4. `gupaco_clo clo r = gpaco_clo clo r r`

## Main Definitions

- `rclo clo R`: Reflexive-transitive closure of R under clo
- `Compatible F clo`: Property that clo (F R) ≤ F (clo R)
- `WCompatible F clo`: Weaker version using gupaco
- `gpaco_clo F clo r rg`: Generalized paco with user-defined closure
- `gupaco_clo F clo r`: Symmetric version (guard = accumulator)

## References

- [Paco paper (POPL 2013)](https://plv.mpi-sws.org/paco/)
- [GPaco paper (CPP 2020)](https://paulhe.com/assets/gpaco.pdf)
- [Paco Coq: gpacoN.v](https://github.com/snu-sf/paco)
-/

namespace Paco

variable {α : Type*}

/-!
## Reflexive-Transitive Closure (rclo)

The core building block for up-to techniques. `rclo clo R` contains:
- Everything in R (base case)
- Everything obtained by applying clo to any relation contained in rclo
-/

/-- Reflexive-transitive closure of a relation under a closure operator.

`rclo clo R` is the smallest relation containing R and closed under clo:
- `rclo_base`: R ⊆ rclo clo R
- `rclo_clo`: If R' ⊆ rclo clo R, then clo R' ⊆ rclo clo R -/
inductive rclo (clo : Rel α → Rel α) (R : Rel α) : Rel α where
  | base (h : R x y) : rclo clo R x y
  | clo (R' : Rel α) (hR' : R' ≤ rclo clo R) (h : clo R' x y) : rclo clo R x y

namespace rclo

variable {clo : Rel α → Rel α} {R S : Rel α}

/-- R is contained in rclo clo R -/
theorem base_le : R ≤ rclo clo R := fun _ _ h => base h

/-- clo R is contained in rclo clo R -/
theorem clo_base : clo R ≤ rclo clo R :=
  fun _ _ h => rclo.clo R base_le h

/-- rclo is monotone in R -/
theorem mono (hRS : R ≤ S) : rclo clo R ≤ rclo clo S := by
  intro x y h
  induction h with
  | base hr => exact base (hRS hr)
  | clo R' _ hclo ih => exact rclo.clo R' ih hclo

/-- rclo is monotone in clo (pointwise) -/
theorem mono_clo {clo₁ clo₂ : Rel α → Rel α} (h : ∀ R, clo₁ R ≤ clo₂ R) :
    rclo clo₁ R ≤ rclo clo₂ R := by
  intro x y hxy
  induction hxy with
  | base hr => exact base hr
  | clo R' _ hclo ih =>
    exact rclo.clo R' ih (h R' _ _ hclo)

/-- clo (rclo clo R) ⊆ rclo clo R -/
theorem clo_rclo : clo (rclo clo R) ≤ rclo clo R :=
  fun _ _ h => rclo.clo (rclo clo R) (fun _ _ hab => hab) h

/-- rclo is idempotent -/
theorem rclo_rclo : rclo clo (rclo clo R) ≤ rclo clo R := by
  intro x y h
  induction h with
  | base hr => exact hr
  | clo R' _ hclo ih => exact rclo.clo R' ih hclo

/-- Union injects into rclo -/
theorem union_le_rclo : rclo clo R ⊔ rclo clo S ≤ rclo clo (R ⊔ S) := by
  apply sup_le
  · exact mono le_sup_left
  · exact mono le_sup_right

/-- rclo is the smallest relation containing R and closed under clo -/
theorem rclo_smallest {R S : Rel α} (hRS : R ≤ S) (hclo : ∀ R', R' ≤ S → clo R' ≤ S) :
    rclo clo R ≤ S := by
  intro x y h
  induction h with
  | base hr => exact hRS _ _ hr
  | clo R' _ hcloR' ih => exact hclo R' ih _ _ hcloR'

/-- rclo with identity closure is identity -/
theorem rclo_id (R : Rel α) : rclo id R = R := by
  apply Rel.le_antisymm
  · apply rclo_smallest (Rel.le_refl R)
    intro R' hR'
    exact hR'
  · exact base_le

end rclo

/-!
## Compatibility

A closure operator `clo` is compatible with `F` if it commutes appropriately
with the generating function.
-/

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

/-!
## Companion (cpn)

The companion is the greatest compatible closure operator. It is defined as the
union of all compatible monotone closures:

  cpn F R x y := ∃ clo, CloMono clo ∧ Compatible F clo ∧ clo R x y

Key properties:
- `cpn_mono`: cpn F is monotone
- `cpn_greatest`: Any compatible monotone clo is ≤ cpn F
- `cpn_compat`: cpn F is itself compatible with F
- `cpn_gupaco`: gupaco F (cpn F) ≤ cpn F (absorption)

References:
- [Paco Coq: cpnN](https://github.com/snu-sf/paco)
- [GPaco paper Section 4](https://paulhe.com/assets/gpaco.pdf)
-/

/-- The companion: greatest compatible closure operator.

`cpn F R x y` holds if there exists a compatible monotone closure `clo` such that
`clo R x y`. This is the union of all compatible closures. -/
inductive cpn (F : MonoRel α) (R : Rel α) : Rel α where
  | intro (clo : Rel α → Rel α) (h_mono : CloMono clo) (h_compat : Compatible F clo)
          (h_clo : clo R x y) : cpn F R x y

namespace cpn

variable {F : MonoRel α} {R S : Rel α}

/-- cpn is monotone: if R ≤ S then cpn F R ≤ cpn F S -/
theorem mono : R ≤ S → cpn F R ≤ cpn F S := by
  intro hRS x y ⟨clo, h_mono, h_compat, h_clo⟩
  exact ⟨clo, h_mono, h_compat, h_mono R S hRS x y h_clo⟩

/-- cpn F is a monotone closure operator -/
theorem cpn_cloMono : CloMono (cpn F) := fun _ _ h => mono h

/-- Any compatible monotone closure is contained in cpn (cpn is greatest) -/
theorem greatest {clo : Rel α → Rel α} (h_mono : CloMono clo) (h_compat : Compatible F clo) :
    clo R ≤ cpn F R := fun _ _ h => ⟨clo, h_mono, h_compat, h⟩

/-- R is contained in cpn F R (via identity closure) -/
theorem base : R ≤ cpn F R := greatest cloMono_id (compatible_id F)

/-- cpn F is compatible with F -/
theorem compat : Compatible F (cpn F) := by
  intro R x y ⟨clo, h_mono, h_compat, h_clo⟩
  have h1 : clo (F R) ≤ F (clo R) := h_compat R
  have h2 : clo R ≤ cpn F R := greatest h_mono h_compat
  have h3 : F (clo R) ≤ F (cpn F R) := F.mono' h2
  exact h3 x y (h1 x y h_clo)

/-- cpn is idempotent: cpn F (cpn F R) ≤ cpn F R -/
theorem cpn_cpn : cpn F (cpn F R) ≤ cpn F R := by
  intro x y ⟨clo, h_mono, h_compat, h_clo⟩
  have h_comp_mono : CloMono (clo ∘ cpn F) := fun R S hRS =>
    h_mono (cpn F R) (cpn F S) (cpn_cloMono R S hRS)
  have h_comp_compat : Compatible F (clo ∘ cpn F) :=
    compatible_comp F h_mono h_compat compat
  have h_le : (clo ∘ cpn F) R ≤ cpn F R := greatest h_comp_mono h_comp_compat
  exact h_le x y h_clo

/-- rclo clo ≤ cpn F when clo is compatible and monotone -/
theorem rclo_le {clo : Rel α → Rel α} (h_mono : CloMono clo) (h_compat : Compatible F clo) :
    rclo clo R ≤ cpn F R := by
  intro x y h
  induction h with
  | base hr => exact base _ _ hr
  | clo R' _ hcloR' ih =>
    have h1 : clo R' ≤ cpn F R' := greatest h_mono h_compat
    have h2 : cpn F R' ≤ cpn F (cpn F R) := mono ih
    have h3 : cpn F (cpn F R) ≤ cpn F R := cpn_cpn
    exact h3 _ _ (h2 _ _ (h1 _ _ hcloR'))

end cpn

/-!
## Composed Generating Function

The key to gpaco: compose F with rclo clo to get a new monotone transformer.
-/

/-- Compose F with rclo clo to get the modified generating function.

This is `compose gf (rclo clo)` from Coq gpaco. -/
def composeRclo (F : MonoRel α) (clo : Rel α → Rel α) : MonoRel α where
  F := F ∘ rclo clo
  mono := by
    intro R S hRS
    exact F.mono' (rclo.mono hRS)

theorem composeRclo_def (F : MonoRel α) (clo : Rel α → Rel α) (R : Rel α) :
    composeRclo F clo R = F (rclo clo R) := rfl

/-!
## GPaco with Closure (gpaco_clo)

The full gpaco definition following Coq:
  gpaco_clo clo r rg = rclo clo (paco (F ∘ rclo clo) (rg ⊔ r) ⊔ r)
-/

/-- Generalized paco with user-defined closure operator.

`gpaco_clo F clo r rg` is the main predicate for up-to coinduction:
- `clo`: User closure operator (e.g., congruence, transitivity)
- `r`: Accumulator (immediately available facts)
- `rg`: Guard (facts available after progress)

Definition: rclo clo (paco (F ∘ rclo clo) (rg ⊔ r) ⊔ r) -/
def gpaco_clo (F : MonoRel α) (clo : Rel α → Rel α) (r rg : Rel α) : Rel α :=
  rclo clo (paco (composeRclo F clo) (rg ⊔ r) ⊔ r)

/-- Symmetric version: guard equals accumulator -/
def gupaco_clo (F : MonoRel α) (clo : Rel α → Rel α) (r : Rel α) : Rel α :=
  gpaco_clo F clo r r

/-!
## GPaco_clo Basic Properties
-/

theorem gpaco_clo_def (F : MonoRel α) (clo : Rel α → Rel α) (r rg : Rel α) :
    gpaco_clo F clo r rg = rclo clo (paco (composeRclo F clo) (rg ⊔ r) ⊔ r) := rfl

theorem gupaco_clo_def (F : MonoRel α) (clo : Rel α → Rel α) (r : Rel α) :
    gupaco_clo F clo r = gpaco_clo F clo r r := rfl

/-- r injects into gpaco_clo -/
theorem r_le_gpaco_clo (F : MonoRel α) (clo : Rel α → Rel α) (r rg : Rel α) :
    r ≤ gpaco_clo F clo r rg := by
  intro x y hr
  exact rclo.base (Or.inr hr)

/-- paco (F ∘ rclo clo) (rg ⊔ r) injects into gpaco_clo -/
theorem paco_le_gpaco_clo (F : MonoRel α) (clo : Rel α → Rel α) (r rg : Rel α) :
    paco (composeRclo F clo) (rg ⊔ r) ≤ gpaco_clo F clo r rg := by
  intro x y hp
  exact rclo.base (Or.inl hp)

/-- gpaco_clo is monotone in r -/
theorem gpaco_clo_mon_r (F : MonoRel α) (clo : Rel α → Rel α) (rg : Rel α)
    {r r' : Rel α} (hr : r ≤ r') : gpaco_clo F clo r rg ≤ gpaco_clo F clo r' rg := by
  unfold gpaco_clo
  apply rclo.mono
  apply sup_le_sup
  · exact paco_mon (composeRclo F clo) (sup_le_sup_left hr rg)
  · exact hr

/-- gpaco_clo is monotone in rg -/
theorem gpaco_clo_mon_rg (F : MonoRel α) (clo : Rel α → Rel α) (r : Rel α)
    {rg rg' : Rel α} (hrg : rg ≤ rg') : gpaco_clo F clo r rg ≤ gpaco_clo F clo r rg' := by
  unfold gpaco_clo
  apply rclo.mono
  apply sup_le_sup_right
  exact paco_mon (composeRclo F clo) (sup_le_sup_right hrg r)

/-- gpaco_clo is monotone in both r and rg -/
theorem gpaco_clo_mon (F : MonoRel α) (clo : Rel α → Rel α)
    {r r' rg rg' : Rel α} (hr : r ≤ r') (hrg : rg ≤ rg') :
    gpaco_clo F clo r rg ≤ gpaco_clo F clo r' rg' :=
  Rel.le_trans (gpaco_clo_mon_r F clo rg hr) (gpaco_clo_mon_rg F clo r' hrg)

/-!
## Weak Compatibility

Weak compatibility is a relaxed version of compatibility that uses gupaco_clo.
The key insight: weak compatibility plus monotonicity implies full compatibility.
-/

/-- Weak compatibility: clo (F R) ≤ F (gupaco_clo F clo R)

This is weaker than compatibility because gupaco_clo F clo R ⊇ clo R.
Weak compatibility can be converted to compatibility via `wcompat_compat`. -/
def WCompatible (F : MonoRel α) (clo : Rel α → Rel α) : Prop :=
  ∀ R, clo (F R) ≤ F (gupaco_clo F clo R)

/-- clo R ≤ gupaco_clo F clo R (clo is contained in gupaco via rclo) -/
theorem clo_le_gupaco_clo (F : MonoRel α) (clo : Rel α → Rel α) (R : Rel α) :
    clo R ≤ gupaco_clo F clo R := by
  intro x y hclo
  simp only [gupaco_clo_def, gpaco_clo_def]
  apply rclo.clo R
  · intro a b hRab
    exact rclo.base (Or.inr hRab)
  · exact hclo

/-- Weak compatibility plus gupaco absorption implies compatibility.

For a closure clo where gupaco_clo F clo R ≤ clo R (absorption), weak
compatibility implies full compatibility. This is used for cpn. -/
theorem wcompat_absorb_compat (F : MonoRel α) {clo : Rel α → Rel α}
    (h_wcompat : WCompatible F clo)
    (h_absorb : ∀ R, gupaco_clo F clo R ≤ clo R) : Compatible F clo := by
  intro R x y hclo
  have h1 := h_wcompat R x y hclo
  exact F.mono' (h_absorb R) x y h1

/-- Compatibility implies weak compatibility (trivially, since clo R ≤ gupaco_clo F clo R) -/
theorem compat_wcompat (F : MonoRel α) {clo : Rel α → Rel α}
    (h_compat : Compatible F clo) : WCompatible F clo := by
  intro R x y hclo
  have h1 := h_compat R x y hclo
  exact F.mono' (clo_le_gupaco_clo F clo R) x y h1

/-!
## Companion: Weak Compatibility and Gupaco Absorption

These lemmas complete the companion construction by showing:
1. cpn is weakly compatible
2. gupaco_clo with cpn absorbs back into cpn
-/

/-- cpn F is weakly compatible with F -/
theorem cpn.wcompat (F : MonoRel α) : WCompatible F (cpn F) := by
  intro R x y ⟨clo, h_mono, h_compat, hclo⟩
  have h1 : clo (F R) ≤ F (clo R) := h_compat R
  have h2 : F (clo R) x y := h1 x y hclo
  have h3 : clo R ≤ cpn F R := cpn.greatest h_mono h_compat
  have h4 : cpn F R ≤ gupaco_clo F (cpn F) R := clo_le_gupaco_clo F (cpn F) R
  have h5 : clo R ≤ gupaco_clo F (cpn F) R := Rel.le_trans h3 h4
  exact F.mono' h5 x y h2

/-- gupaco_clo F clo is monotone as a closure operator (in the relation argument) -/
theorem gupaco_clo_cloMono (F : MonoRel α) (clo : Rel α → Rel α) :
    CloMono (gupaco_clo F clo) := by
  intro R S hRS
  simp only [gupaco_clo_def]
  exact gpaco_clo_mon F clo hRS hRS

/-- If clo is weakly compatible, then gupaco_clo F clo is (strongly) compatible.

Note: The general proof requires gupaco idempotence which is circular.
This lemma is proven for cpn specifically in `cpn.gupaco_compat`. -/
theorem wcompat_compat_gupaco (F : MonoRel α) {clo : Rel α → Rel α}
    (h_mono : CloMono clo) (h_wcompat : WCompatible F clo)
    (h_idemp : ∀ R, gupaco_clo F clo (gupaco_clo F clo R) ≤ gupaco_clo F clo R) :
    Compatible F (gupaco_clo F clo) := by
  intro R
  simp only [gupaco_clo_def, gpaco_clo_def, sup_idem]
  intro x y hgup
  induction hgup with
  | @base x y hbase =>
    cases hbase with
    | inl hpaco =>
      have hFR_le : F R ≤ (composeRclo F clo) R := fun u v h => F.mono' rclo.base_le u v h
      have hpaco' := paco_mon (composeRclo F clo) hFR_le x y hpaco
      have hunf := paco_unfold (composeRclo F clo) R x y hpaco'
      simp only [composeRclo_def, upaco] at hunf
      exact F.mono' (rclo.mono (sup_le_sup_right (fun u v h => Or.inl h) R)) x y hunf
    | inr hFR =>
      have h1 : R ≤ rclo clo (paco (composeRclo F clo) R ⊔ R) := fun u v h => rclo.base (Or.inr h)
      exact F.mono' h1 x y hFR
  | @clo x y R' hR' hcloR' ih =>
    have h1 : clo R' ≤ clo (F (rclo clo (paco (composeRclo F clo) R ⊔ R))) := h_mono R' _ ih
    have h2 := h_wcompat (rclo clo (paco (composeRclo F clo) R ⊔ R)) x y (h1 x y hcloR')
    simp only [gupaco_clo_def, gpaco_clo_def, sup_idem] at h2
    exact F.mono' (h_idemp R) x y h2

/-- cpn F X ≤ rclo (cpn F) X (cpn embeds into rclo via rclo.clo) -/
theorem cpn.le_rclo (F : MonoRel α) (X : Rel α) : cpn F X ≤ rclo (cpn F) X := by
  intro x y ⟨clo, h_mono, h_compat, hclo⟩
  have h1 : clo X ≤ cpn F X := cpn.greatest h_mono h_compat
  apply rclo.clo X
  · exact rclo.base_le
  · exact h1 x y hclo

/-- gupaco_clo F (cpn F) is compatible with F.

This is proven directly without requiring gupaco idempotence, using
the special properties of cpn (greatest compatible closure). -/
theorem cpn.gupaco_compat (F : MonoRel α) : Compatible F (gupaco_clo F (cpn F)) := by
  intro R
  simp only [gupaco_clo_def, gpaco_clo_def, sup_idem]
  intro x y hgup
  induction hgup with
  | @base x y hbase =>
    cases hbase with
    | inl hpaco =>
      have hFR_le : F R ≤ (composeRclo F (cpn F)) R := fun u v h => F.mono' rclo.base_le u v h
      have hpaco' := paco_mon (composeRclo F (cpn F)) hFR_le x y hpaco
      have hunf := paco_unfold (composeRclo F (cpn F)) R x y hpaco'
      simp only [composeRclo_def, upaco] at hunf
      exact F.mono' (rclo.mono (sup_le_sup_right (fun u v h => Or.inl h) R)) x y hunf
    | inr hFR =>
      have h1 : R ≤ rclo (cpn F) (paco (composeRclo F (cpn F)) R ⊔ R) := fun u v h => rclo.base (Or.inr h)
      exact F.mono' h1 x y hFR
  | @clo x y R' hR' hcloR' ih =>
    obtain ⟨clo, h_mono, h_compat, hclo⟩ := hcloR'
    have h1 : clo R' ≤ clo (F (rclo (cpn F) (paco (composeRclo F (cpn F)) R ⊔ R))) := h_mono R' _ ih
    let S := rclo (cpn F) (paco (composeRclo F (cpn F)) R ⊔ R)
    have h2 : clo (F S) ≤ F (clo S) := h_compat S
    have h3 : F (clo S) x y := h2 x y (h1 x y hclo)
    have h4 : clo S ≤ cpn F S := cpn.greatest h_mono h_compat
    have h5 : cpn F S ≤ cpn F (cpn F (paco (composeRclo F (cpn F)) R ⊔ R)) := by
      apply cpn.mono
      exact cpn.rclo_le cpn.cpn_cloMono cpn.compat
    have h6 : cpn F (cpn F (paco (composeRclo F (cpn F)) R ⊔ R)) ≤
              cpn F (paco (composeRclo F (cpn F)) R ⊔ R) := cpn.cpn_cpn
    have h7 : cpn F (paco (composeRclo F (cpn F)) R ⊔ R) ≤ S := cpn.le_rclo F _
    have h8 : clo S ≤ S := Rel.le_trans (Rel.le_trans (Rel.le_trans h4 h5) h6) h7
    exact F.mono' h8 x y h3

/-- gupaco_clo with cpn absorbs into cpn: gupaco_clo F (cpn F) R ≤ cpn F R

This is the key absorption lemma. The proof uses cpn_greatest: since
gupaco_clo F (cpn F) is compatible (via cpn.gupaco_compat),
it must be ≤ cpn F (the greatest compatible closure). -/
theorem cpn.gupaco (F : MonoRel α) (R : Rel α) :
    gupaco_clo F (cpn F) R ≤ cpn F R := by
  have h_compat : Compatible F (gupaco_clo F (cpn F)) := cpn.gupaco_compat F
  have h_mono : CloMono (gupaco_clo F (cpn F)) := gupaco_clo_cloMono F (cpn F)
  exact cpn.greatest h_mono h_compat

/-- gupaco_clo F (cpn F) equals cpn F (they absorb each other) -/
theorem cpn.gupaco_eq (F : MonoRel α) (R : Rel α) :
    gupaco_clo F (cpn F) R = cpn F R := by
  apply Rel.le_antisymm
  · exact cpn.gupaco F R
  · intro x y hcpn
    simp only [gupaco_clo_def, gpaco_clo_def, sup_idem]
    -- cpn F R ≤ rclo (cpn F) R ≤ rclo (cpn F) (paco G R ⊔ R)
    apply rclo.clo R rclo.base_le
    exact hcpn

/-- cpn absorbs upaco: cpn F (upaco G S) ≤ cpn F S when G = composeRclo F clo and clo ≤ cpn F -/
theorem cpn.upaco_absorb (F : MonoRel α) (clo : Rel α → Rel α)
    (h_mono : CloMono clo) (h_compat : Compatible F clo) (S : Rel α) :
    cpn F (upaco (composeRclo F clo) S) ≤ cpn F S := by
  -- upaco G S = paco G S ⊔ S ≤ gupaco_clo F clo S (by rclo.base_le)
  -- gupaco_clo F clo S ≤ gupaco_clo F (cpn F) S (by mono in clo)
  -- gupaco_clo F (cpn F) S = cpn F S
  have h1 : upaco (composeRclo F clo) S ≤ gupaco_clo F clo S := by
    intro x y hup
    simp only [gupaco_clo_def, gpaco_clo_def, sup_idem]
    exact rclo.base hup
  have h_clo_le : ∀ R, clo R ≤ cpn F R := fun R => cpn.greatest h_mono h_compat
  have h2 : gupaco_clo F clo S ≤ gupaco_clo F (cpn F) S := by
    simp only [gupaco_clo_def, gpaco_clo_def, sup_idem]
    apply rclo.mono_clo h_clo_le
  have h3 : gupaco_clo F (cpn F) S = cpn F S := cpn.gupaco_eq F S
  calc cpn F (upaco (composeRclo F clo) S)
      ≤ cpn F (gupaco_clo F clo S) := cpn.mono h1
    _ ≤ cpn F (gupaco_clo F (cpn F) S) := cpn.mono h2
    _ = cpn F (cpn F S) := by rw [h3]
    _ ≤ cpn F S := cpn.cpn_cpn

/-!
## GPaco_clo Coinduction Principle

The main coinduction principle: to prove gpaco_clo F clo r rg x y,
provide a relation R with R x y such that for any rr extending rg ⊔ R,
we have R ⊆ gpaco_clo F clo r rr.
-/

/-- Helper: rclo preserves containment in gpaco_clo -/
theorem rclo_gpaco_clo_le (F : MonoRel α) (clo : Rel α → Rel α) (r rg rg' : Rel α)
    (hrg : rg ≤ rg') :
    rclo clo (paco (composeRclo F clo) (rg ⊔ r) ⊔ r) ≤ gpaco_clo F clo r rg' := by
  unfold gpaco_clo
  apply rclo.mono
  apply sup_le_sup_right
  exact paco_mon (composeRclo F clo) (sup_le_sup_right hrg r)

/-- Full coinduction principle for gpaco_clo (Coq's gpacoN_cofix).

To prove `l ≤ gpaco_clo F clo r rg`, show that for any `rr` with
`rg ≤ rr` (INC) and `l ≤ rr` (CIH), we have `l ≤ gpaco_clo F clo r rr`.

The key insight (from Coq): First get `IN: l ≤ gpaco r (rg ⊔ l)` by instantiating
OBG with rr = rg ⊔ l. Then use coinduction to collapse `paco P ((rg ⊔ l) ⊔ r)`
back to `paco P (rg ⊔ r)`. The `l` elements get transformed via IN into the
gpaco structure, which lands in `rclo clo (W ⊔ S)` for the coinductive witness. -/
theorem gpaco_clo_coind (F : MonoRel α) (clo : Rel α → Rel α) (r rg : Rel α)
    (l : Rel α)
    (OBG : ∀ rr, rg ≤ rr → l ≤ rr → l ≤ gpaco_clo F clo r rr) :
    l ≤ gpaco_clo F clo r rg := by
  have IN : l ≤ gpaco_clo F clo r (rg ⊔ l) := OBG (rg ⊔ l) le_sup_left le_sup_right
  intro x y hlxy
  have hgpaco := IN x y hlxy
  simp only [gpaco_clo_def] at hgpaco ⊢
  have h_inner : paco (composeRclo F clo) ((rg ⊔ l) ⊔ r) ⊔ r ≤
                 rclo clo (paco (composeRclo F clo) (rg ⊔ r) ⊔ r) := by
    apply sup_le
    · intro a b hpaco_ab
      apply rclo.base
      left
      apply paco_coind (composeRclo F clo) (paco (composeRclo F clo) ((rg ⊔ l) ⊔ r)) (rg ⊔ r)
      · intro u v huv
        have h_unfold := paco_unfold (composeRclo F clo) ((rg ⊔ l) ⊔ r) u v huv
        simp only [composeRclo_def] at h_unfold ⊢
        have h_rclo_le : rclo clo (upaco (composeRclo F clo) ((rg ⊔ l) ⊔ r)) ≤
                         rclo clo (paco (composeRclo F clo) ((rg ⊔ l) ⊔ r) ⊔ (rg ⊔ r)) := by
          apply rclo.mono
          intro x' y' hup
          simp only [upaco, Rel.union_apply] at hup
          cases hup with
          | inl hp => exact rclo.base (Or.inl hp)
          | inr hrglr =>
            simp only [Rel.union_apply] at hrglr
            cases hrglr with
            | inl hrgl =>
              cases hrgl with
              | inl hrg => exact rclo.base (Or.inr (Or.inl hrg))
              | inr hl' =>
                have hIN := IN x' y' hl'
                simp only [gpaco_clo_def] at hIN
                have h_r_le : paco (composeRclo F clo) ((rg ⊔ l) ⊔ r) ⊔ r ≤
                              paco (composeRclo F clo) ((rg ⊔ l) ⊔ r) ⊔ (rg ⊔ r) := by
                  apply sup_le_sup_left
                  intro x'' y'' hr''
                  right; exact hr''
                exact rclo.mono h_r_le hIN
            | inr hr' => exact rclo.base (Or.inr (Or.inr hr'))
        apply F.mono' h_rclo_le u v h_unfold
      · exact hpaco_ab
    · intro a b hr_ab
      exact rclo.base (Or.inr hr_ab)
  exact rclo.mono h_inner hgpaco

/-- Simple coinduction for gpaco_clo: prove via paco with F-progress.

To prove `gpaco_clo F clo r rg x y`, find R with R x y such that
R ⊆ F (rclo clo (R ⊔ upaco (F ∘ rclo clo) (rg ⊔ r))) ⊔ r.

Note: When R a b gives r a b (base case), no F-progress is needed. -/
theorem gpaco_clo_cofix (F : MonoRel α) (clo : Rel α → Rel α) (r rg : Rel α)
    (R : Rel α) {x y : α}
    (hR : R ≤ F (rclo clo (R ⊔ upaco (composeRclo F clo) (rg ⊔ r))) ⊔ r)
    (hxy : R x y) : gpaco_clo F clo r rg x y := by
  unfold gpaco_clo
  apply rclo.base
  -- Either in paco part or r part
  cases hR x y hxy with
  | inl hF =>
    -- hF : F (rclo clo (R ⊔ upaco ...)) x y - productive case
    left
    -- Define the productive subset: R elements that make F-progress
    let R' : Rel α := fun a b => R a b ∧ ∃ h : R a b, (F (rclo clo (R ⊔ upaco (composeRclo F clo) (rg ⊔ r))) a b)
    apply paco_coind (composeRclo F clo) (R' ⊔ paco (composeRclo F clo) (rg ⊔ r)) (rg ⊔ r)
    · intro a b hab
      simp only [composeRclo_def]
      cases hab with
      | inl hR'ab =>
        obtain ⟨hRab, _, hFab⟩ := hR'ab
        apply F.mono' _ a b hFab
        apply rclo.mono
        intro u v huv
        cases huv with
        | inl hRuv =>
          -- R u v - check if productive or base
          cases hR u v hRuv with
          | inl hFuv => left; left; exact ⟨hRuv, hRuv, hFuv⟩
          | inr hruv => right; right; exact hruv
        | inr hup =>
          simp only [upaco, Rel.union_apply] at hup ⊢
          cases hup with
          | inl hp => left; right; exact hp
          | inr hrg => right; exact hrg
      | inr hpaco =>
        have h := paco_unfold (composeRclo F clo) (rg ⊔ r) a b hpaco
        simp only [composeRclo_def] at h
        apply F.mono' _ a b h
        apply rclo.mono
        intro u v huv
        simp only [upaco, Rel.union_apply] at huv ⊢
        cases huv with
        | inl hp => left; right; exact hp
        | inr hrg => right; exact hrg
    · left; exact ⟨hxy, hxy, hF⟩
  | inr hr =>
    -- Base case: r x y, no coinduction needed
    right; exact hr

/-!
## Relationship to GPaco (without closure)

When clo = id, gpaco_clo reduces to something equivalent to gpaco.
-/

/-- With identity closure, composeRclo simplifies to F -/
theorem composeRclo_id (F : MonoRel α) : composeRclo F id = F := by
  cases F with
  | mk f hf =>
    simp only [composeRclo]
    congr 1
    funext R
    simp only [Function.comp_apply, rclo.rclo_id]

/-- With identity closure, gpaco_clo simplifies to gpaco -/
theorem gpaco_clo_id (F : MonoRel α) (r rg : Rel α) :
    gpaco_clo F id r rg = paco F (rg ⊔ r) ⊔ r := by
  simp only [gpaco_clo_def, rclo.rclo_id, composeRclo_id]

/-!
## Accumulation in GPaco_clo
-/

/-- gupaco_clo absorbs into gpaco_clo (requires compatible monotone closure).

This is a key accumulation lemma: facts proven via gupaco_clo can be accumulated
back into gpaco_clo, enabling compositional proofs.

Proof strategy (following Coq's paco library):
1. Use gpaco_clo_coind with l = gupaco_clo F clo G where G = gpaco_clo F clo r rg
2. The OBG obligation gives us INC: rg ≤ rr and CIH: l ≤ rr
3. Using CIH, we bound paco P G ⊔ G by rr
4. This allows transforming gupaco_clo into gpaco_clo -/
theorem gpaco_clo_gupaco (F : MonoRel α) (clo : Rel α → Rel α)
    (h_mono : CloMono clo) (h_compat : Compatible F clo)
    (r rg : Rel α) :
    gupaco_clo F clo (gpaco_clo F clo r rg) ≤ gpaco_clo F clo r rg := by
  let G := gpaco_clo F clo r rg
  let P := composeRclo F clo
  apply gpaco_clo_coind F clo r rg (gupaco_clo F clo G)
  intro rr INC CIH
  simp only [gupaco_clo_def, gpaco_clo_def]
  have hG_simp : G ⊔ G = G := sup_idem G
  simp only [gpaco_clo_def] at hG_simp
  rw [hG_simp]
  apply rclo.mono
  have h_pacoG_le_rr : paco P G ≤ rr := by
    intro x y hpaco
    have h1 : rclo clo (paco P G ⊔ G) x y := rclo.base (Or.inl hpaco)
    exact CIH x y h1
  have h_G_le_rr : G ≤ rr := by
    intro x y hG
    have h1 : rclo clo (paco P G ⊔ G) x y := rclo.base (Or.inr hG)
    exact CIH x y h1
  have h_sup_le_rr : paco P G ⊔ G ≤ rr := sup_le h_pacoG_le_rr h_G_le_rr
  have h_rr_le_target : rr ≤ paco P (rr ⊔ r) ⊔ r := by
    intro x y hrr
    right; left; exact hrr
  have h_to_target : paco P G ⊔ G ≤ paco P (rr ⊔ r) ⊔ r :=
    Rel.le_trans h_sup_le_rr h_rr_le_target
  intro x y hxy
  exact rclo.base (h_to_target x y hxy)

/-- Specialized gupaco absorption for the companion (cpn F).

This version is fully provable because cpn has the special property that
`gupaco_clo F (cpn F) R = cpn F R` (by cpn.gupaco_eq). -/
theorem gpaco_clo_gupaco_cpn (F : MonoRel α) (r rg : Rel α) :
    gupaco_clo F (cpn F) (gpaco_clo F (cpn F) r rg) ≤ gpaco_clo F (cpn F) r rg := by
  -- gupaco_clo F (cpn F) X = cpn F X by cpn.gupaco_eq
  -- So we need: cpn F (gpaco_clo F (cpn F) r rg) ≤ gpaco_clo F (cpn F) r rg
  --
  -- gpaco_clo F (cpn F) r rg = rclo (cpn F) (paco G (rg ⊔ r) ⊔ r) where G = composeRclo F (cpn F)
  --
  -- By cpn.rclo_le: rclo (cpn F) X ≤ cpn F X (since cpn F is compatible monotone)
  -- So gpaco_clo F (cpn F) r rg ≤ cpn F (paco G (rg ⊔ r) ⊔ r)
  --
  -- cpn F (cpn F X) ≤ cpn F X by cpn.cpn_cpn
  -- So cpn F (gpaco_clo F (cpn F) r rg) ≤ cpn F (cpn F (paco G (rg ⊔ r) ⊔ r))
  --                                     ≤ cpn F (paco G (rg ⊔ r) ⊔ r)
  --
  -- Now we need: cpn F (paco G (rg ⊔ r) ⊔ r) ≤ rclo (cpn F) (paco G (rg ⊔ r) ⊔ r)
  -- This holds by rclo.clo_base: cpn F X ≤ rclo (cpn F) X
  have h_gupaco_eq : gupaco_clo F (cpn F) (gpaco_clo F (cpn F) r rg) =
                     cpn F (gpaco_clo F (cpn F) r rg) := cpn.gupaco_eq F (gpaco_clo F (cpn F) r rg)
  rw [h_gupaco_eq]
  -- Goal: cpn F (gpaco_clo F (cpn F) r rg) ≤ gpaco_clo F (cpn F) r rg
  -- gpaco_clo F (cpn F) r rg = rclo (cpn F) (paco G (rg ⊔ r) ⊔ r)
  simp only [gpaco_clo_def]
  let G := composeRclo F (cpn F)
  -- Step 1: gpaco ≤ cpn F (paco G (rg ⊔ r) ⊔ r)
  have h1 : rclo (cpn F) (paco G (rg ⊔ r) ⊔ r) ≤ cpn F (paco G (rg ⊔ r) ⊔ r) :=
    cpn.rclo_le cpn.cpn_cloMono cpn.compat
  -- Step 2: cpn F (gpaco) ≤ cpn F (cpn F X)
  have h2 : cpn F (rclo (cpn F) (paco G (rg ⊔ r) ⊔ r)) ≤
            cpn F (cpn F (paco G (rg ⊔ r) ⊔ r)) := cpn.mono h1
  -- Step 3: cpn F (cpn F X) ≤ cpn F X
  have h3 : cpn F (cpn F (paco G (rg ⊔ r) ⊔ r)) ≤ cpn F (paco G (rg ⊔ r) ⊔ r) := cpn.cpn_cpn
  -- Step 4: cpn F X ≤ rclo (cpn F) X
  have h4 : cpn F (paco G (rg ⊔ r) ⊔ r) ≤ rclo (cpn F) (paco G (rg ⊔ r) ⊔ r) := rclo.clo_base
  -- Chain: cpn F (gpaco) ≤ cpn F (cpn F X) ≤ cpn F X ≤ rclo (cpn F) X = gpaco
  exact Rel.le_trans (Rel.le_trans h2 h3) h4

/-!
## Compatibility and GPaco_clo

When clo is compatible, gpaco_clo proofs can be converted to standard paco proofs.
-/

/-- gfp F is closed under compatible closure -/
theorem gfp_closed_clo (F : MonoRel α) (clo : Rel α → Rel α)
    (_h_mono : CloMono clo) (h_compat : Compatible F clo) :
    clo F.toOrderHom.gfp ≤ F.toOrderHom.gfp := by
  intro x y hclo
  -- clo (gfp F) x y
  -- gfp F = F (gfp F), so clo (gfp F) ≤ clo (F (gfp F))
  -- By compatibility: clo (F (gfp F)) ≤ F (clo (gfp F))
  -- We need to show F.toOrderHom.gfp x y
  -- Use that gfp is a fixed point and clo doesn't escape
  have hgfp_eq : F.toOrderHom.gfp = F F.toOrderHom.gfp := F.toOrderHom.map_gfp.symm
  -- Show clo (gfp F) ≤ gfp F by showing clo (gfp F) ≤ F (gfp F)
  -- clo (gfp F) = clo (F (gfp F)) ≤ F (clo (gfp F)) by compatibility
  -- So clo (gfp F) is a post-fixpoint... but this is circular
  -- Actually: clo (gfp F) ⊔ gfp F is a post-fixpoint
  have hpost : clo F.toOrderHom.gfp ⊔ F.toOrderHom.gfp ≤ F (clo F.toOrderHom.gfp ⊔ F.toOrderHom.gfp) := by
    apply sup_le
    · calc clo F.toOrderHom.gfp = clo (F F.toOrderHom.gfp) := congrArg clo hgfp_eq
        _ ≤ F (clo F.toOrderHom.gfp) := h_compat F.toOrderHom.gfp
        _ ≤ F (clo F.toOrderHom.gfp ⊔ F.toOrderHom.gfp) := F.mono' le_sup_left
    · calc F.toOrderHom.gfp = F F.toOrderHom.gfp := hgfp_eq
        _ ≤ F (clo F.toOrderHom.gfp ⊔ F.toOrderHom.gfp) := F.mono' le_sup_right
  have hle := OrderHom.le_gfp F.toOrderHom hpost
  exact hle x y (Or.inl hclo)

/-- gfp F is closed under rclo of compatible monotone closure -/
theorem gfp_closed_rclo (F : MonoRel α) (clo : Rel α → Rel α)
    (h_mono : CloMono clo) (h_compat : Compatible F clo) :
    rclo clo F.toOrderHom.gfp ≤ F.toOrderHom.gfp := by
  intro x y h
  induction h with
  | base hr => exact hr
  | clo R' _ hcloR' ih =>
    exact gfp_closed_clo F clo h_mono h_compat _ _ (h_mono R' _ ih _ _ hcloR')

/-- If clo is compatible, gpaco_clo is contained in gfp F -/
theorem gpaco_clo_final (F : MonoRel α) (clo : Rel α → Rel α)
    (h_mono : CloMono clo) (h_compat : Compatible F clo)
    (r rg : Rel α) (hr : r ≤ F.toOrderHom.gfp) (hrg : rg ≤ F.toOrderHom.gfp) :
    gpaco_clo F clo r rg ≤ F.toOrderHom.gfp := by
  -- gpaco_clo = rclo clo (paco (composeRclo F clo) (rg ⊔ r) ⊔ r)
  simp only [gpaco_clo_def]
  -- Show: rclo clo (paco ... ⊔ r) ≤ gfp F
  -- Strategy: show inner ≤ gfp F, then use rclo clo (gfp F) ≤ gfp F
  -- Helper: gfp F is a pre-fixed point of composeRclo F clo
  have hgfp_prefixed : F.toOrderHom.gfp ≤ (composeRclo F clo).toOrderHom F.toOrderHom.gfp := by
    intro u v huv
    -- Goal: (composeRclo F clo) (gfp F) u v, i.e., F (rclo clo (gfp F)) u v
    have hgfp_eq : F.toOrderHom.gfp = F F.toOrderHom.gfp := F.toOrderHom.map_gfp.symm
    rw [hgfp_eq] at huv
    exact F.mono' rclo.base_le u v huv
  -- Helper: gfp F ≤ gfp (composeRclo F clo) since gfp F is a pre-fixed point
  have hgfp_le_compose : F.toOrderHom.gfp ≤ (composeRclo F clo).toOrderHom.gfp :=
    OrderHom.le_gfp (composeRclo F clo).toOrderHom hgfp_prefixed
  -- Helper: gfp (composeRclo F clo) ≤ gfp F when clo is compatible
  -- Key insight: Use rclo idempotence to show gfp (F ∘ rclo clo) is a post-fixpoint of F
  have hcompose_le_gfp : (composeRclo F clo).toOrderHom.gfp ≤ F.toOrderHom.gfp := by
    -- Abbreviation for the composed transformer
    set G := composeRclo F clo with hG_def
    set R := G.toOrderHom.gfp with hR_def
    -- Step 1: R = G R = F (rclo clo R) [fixed point property]
    have hR_eq : R = G.F R := G.toOrderHom.map_gfp.symm
    -- Step 2: G.F S = F.F (rclo clo S) by definition
    have hGF_eq : ∀ S, G.F S = F.F (rclo clo S) := fun S => rfl
    -- Step 3: rclo idempotence
    have h_idem : rclo clo (rclo clo R) = rclo clo R :=
      Rel.le_antisymm rclo.rclo_rclo rclo.base_le
    -- Step 4: rclo clo R is a post-fixpoint of G
    have hrclo_post_G : rclo clo R ≤ G.F (rclo clo R) := by
      -- G.F (rclo clo R) = F (rclo clo (rclo clo R)) = F (rclo clo R) by idempotence
      rw [hGF_eq, h_idem]
      -- Goal: rclo clo R ≤ F (rclo clo R)
      -- R ⊆ rclo clo R, and R = G R = F (rclo clo R)
      -- So rclo clo R ⊆ rclo clo (F (rclo clo R)) ⊆ F (rclo clo R) by compatibility
      have h1 : rclo clo R ≤ rclo clo (F.F (rclo clo R)) := by
        apply rclo.mono
        rw [← hGF_eq, ← hR_eq]
      have h2 : rclo clo (F.F (rclo clo R)) ≤ F.F (rclo clo (rclo clo R)) :=
        rclo_compatible F h_mono h_compat (rclo clo R)
      calc rclo clo R
          ≤ rclo clo (F.F (rclo clo R)) := h1
        _ ≤ F.F (rclo clo (rclo clo R)) := h2
        _ = F.F (rclo clo R) := by rw [h_idem]
    -- Step 5: Since R is greatest post-fixpoint of G, rclo clo R ≤ R
    have hrclo_le_R : rclo clo R ≤ R := OrderHom.le_gfp G.toOrderHom hrclo_post_G
    -- Step 6: R is a post-fixpoint of F
    have hR_post_F : R ≤ F.F R := by
      calc R = G.F R := hR_eq
        _ = F.F (rclo clo R) := hGF_eq R
        _ ≤ F.F R := F.mono' hrclo_le_R
    -- Step 7: Therefore R ≤ gfp F
    exact OrderHom.le_gfp F.toOrderHom hR_post_F
  -- Show paco ... ⊔ r ≤ gfp F
  have hinner : paco (composeRclo F clo) (rg ⊔ r) ⊔ r ≤ F.toOrderHom.gfp := by
    apply sup_le _ hr
    -- paco (composeRclo F clo) (rg ⊔ r) ≤ gfp F
    intro x y hpaco
    have hparam_le : rg ⊔ r ≤ (composeRclo F clo).toOrderHom.gfp := by
      apply sup_le
      · exact Rel.le_trans hrg hgfp_le_compose
      · exact Rel.le_trans hr hgfp_le_compose
    have hpaco_le := paco_final (composeRclo F clo) (rg ⊔ r) hparam_le x y hpaco
    exact hcompose_le_gfp x y hpaco_le
  -- Now: rclo clo (inner) ≤ rclo clo (gfp F) ≤ gfp F
  calc rclo clo (paco (composeRclo F clo) (rg ⊔ r) ⊔ r)
      ≤ rclo clo F.toOrderHom.gfp := rclo.mono hinner
    _ ≤ F.toOrderHom.gfp := gfp_closed_rclo F clo h_mono h_compat

/-!
## Common Up-To Closures

Standard closure operators that are commonly used with up-to techniques.
-/

/-- Reflexive closure: adds identity pairs -/
def reflClosure (R : Rel α) : Rel α := fun x y => x = y ∨ R x y

/-- Symmetric closure: adds reverse pairs -/
def symmClosure (R : Rel α) : Rel α := fun x y => R x y ∨ R y x

/-- Transitive closure: iteratively applies R -/
inductive transClosure (R : Rel α) : Rel α where
  | base (h : R x y) : transClosure R x y
  | trans (h₁ : transClosure R x z) (h₂ : transClosure R z y) : transClosure R x y

/-- Reflexive-transitive closure -/
inductive rtClosure (R : Rel α) : Rel α where
  | refl : rtClosure R x x
  | base (h : R x y) : rtClosure R x y
  | trans (h₁ : rtClosure R x z) (h₂ : rtClosure R z y) : rtClosure R x y

/-- Equivalence closure (reflexive, symmetric, transitive) -/
inductive eqvClosure (R : Rel α) : Rel α where
  | refl : eqvClosure R x x
  | base (h : R x y) : eqvClosure R x y
  | symm (h : eqvClosure R x y) : eqvClosure R y x
  | trans (h₁ : eqvClosure R x z) (h₂ : eqvClosure R z y) : eqvClosure R x y

/-- Congruence closure: lift R through a function -/
def congClosure (f : α → α) (R : Rel α) : Rel α :=
  fun x y => ∃ a b, R a b ∧ x = f a ∧ y = f b

/-!
### Closure Properties
-/

/-- reflClosure is monotone -/
theorem reflClosure_mono : CloMono (reflClosure (α := α)) := by
  intro R S hRS x y h
  cases h with
  | inl heq => left; exact heq
  | inr hR => right; exact hRS x y hR

/-- symmClosure is monotone -/
theorem symmClosure_mono : CloMono (symmClosure (α := α)) := by
  intro R S hRS x y h
  cases h with
  | inl hR => left; exact hRS x y hR
  | inr hR => right; exact hRS y x hR

/-- transClosure is monotone -/
theorem transClosure_mono : CloMono (transClosure (α := α)) := by
  intro R S hRS x y h
  induction h with
  | base hR => exact transClosure.base (hRS _ _ hR)
  | trans _ _ ih₁ ih₂ => exact transClosure.trans ih₁ ih₂

/-- rtClosure is monotone -/
theorem rtClosure_mono : CloMono (rtClosure (α := α)) := by
  intro R S hRS x y h
  induction h with
  | refl => exact rtClosure.refl
  | base hR => exact rtClosure.base (hRS _ _ hR)
  | trans _ _ ih₁ ih₂ => exact rtClosure.trans ih₁ ih₂

/-- eqvClosure is monotone -/
theorem eqvClosure_mono : CloMono (eqvClosure (α := α)) := by
  intro R S hRS x y h
  induction h with
  | refl => exact eqvClosure.refl
  | base hR => exact eqvClosure.base (hRS _ _ hR)
  | symm _ ih => exact eqvClosure.symm ih
  | trans _ _ ih₁ ih₂ => exact eqvClosure.trans ih₁ ih₂

/-- congClosure is monotone (in R) for fixed f -/
theorem congClosure_mono (f : α → α) : CloMono (congClosure f) := by
  intro R S hRS x y ⟨a, b, hR, hxa, hyb⟩
  exact ⟨a, b, hRS a b hR, hxa, hyb⟩

/-!
### Compatibility Results

Note: Compatibility of these closures depends on the structure of F.
The following are conditional results that hold when F has certain properties.
-/

/-- reflClosure is compatible if F is reflexive (F R x x for all x when R is reflexive) -/
theorem reflClosure_compatible (F : MonoRel α)
    (hF_refl : ∀ R : Rel α, (∀ x, R x x) → ∀ x, F R x x) :
    Compatible F reflClosure := by
  intro R x y h
  cases h with
  | inl heq =>
    subst heq
    apply hF_refl (reflClosure R)
    intro z
    left; rfl
  | inr hFR =>
    apply F.mono' (fun a b hab => Or.inr hab)
    exact hFR

/-- symmClosure is compatible if F commutes with symmetry -/
theorem symmClosure_compatible (F : MonoRel α)
    (hF_symm : ∀ R x y, F R x y → F (symmClosure R) y x) :
    Compatible F symmClosure := by
  intro R x y h
  cases h with
  | inl hFR =>
    apply F.mono' (fun a b hab => Or.inl hab)
    exact hFR
  | inr hFR =>
    exact hF_symm R y x hFR

/-- Congruence closure is compatible if F respects the function f -/
theorem congClosure_compatible (F : MonoRel α) (f : α → α)
    (hF_cong : ∀ R x y, F R x y → F (congClosure f R) (f x) (f y)) :
    Compatible F (congClosure f) := by
  intro R x y ⟨a, b, hFab, hxa, hyb⟩
  subst hxa hyb
  exact hF_cong R a b hFab

end Paco
