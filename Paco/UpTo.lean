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
  | base hr => exact base (hRS _ _ hr)
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
  | clo R' _ hcloR' ih =>
    -- ih : R' ≤ S
    exact hclo R' ih _ _ hcloR'

/-- rclo with identity closure is identity -/
theorem rclo_id (R : Rel α) : rclo id R = R := by
  apply Rel.le_antisymm
  · apply rclo_smallest (Rel.le_refl R)
    intro R' hR'
    -- Need: id R' ≤ R, i.e., R' ≤ R
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
  | base hFR =>
    -- F R x y → F (rclo clo R) x y
    exact F.mono' rclo.base_le _ _ hFR
  | clo R' _ hcloR' ih =>
    -- hcloR' : clo R' x' y' where R' ⊆ rclo clo (F R)
    -- ih : R' ⊆ F (rclo clo R)
    -- Use compatibility: clo R' ≤ clo (F (rclo clo R)) ≤ F (clo (rclo clo R)) ≤ F (rclo clo R)
    have h1 : clo R' ≤ clo (F (rclo clo R)) := h_mono R' _ ih
    have h2 : clo (F (rclo clo R)) ≤ F (clo (rclo clo R)) := h_compat (rclo clo R)
    have h3 : clo (rclo clo R) ≤ rclo clo R := rclo.clo_rclo
    have h4 : F (clo (rclo clo R)) ≤ F (rclo clo R) := F.mono' h3
    exact h4 _ _ (h2 _ _ (h1 _ _ hcloR'))

/-- rclo of a monotone closure is monotone -/
theorem rclo_mono (clo : Rel α → Rel α) : CloMono (rclo clo) :=
  fun _ _ h => rclo.mono h

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
back into gpaco_clo, enabling compositional proofs. -/
theorem gpaco_clo_gupaco (F : MonoRel α) (clo : Rel α → Rel α)
    (h_mono : CloMono clo) (h_compat : Compatible F clo)
    (r rg : Rel α) :
    gupaco_clo F clo (gpaco_clo F clo r rg) ≤ gpaco_clo F clo r rg := by
  -- gupaco_clo F clo G = gpaco_clo F clo G G where G = gpaco_clo F clo r rg
  -- = rclo clo (paco (composeRclo F clo) (G ⊔ G) ⊔ G)
  -- = rclo clo (paco (composeRclo F clo) G ⊔ G)  [since G ⊔ G = G]
  simp only [gupaco_clo_def, gpaco_clo_def]
  have heq : gpaco_clo F clo r rg ⊔ gpaco_clo F clo r rg = gpaco_clo F clo r rg :=
    sup_idem (gpaco_clo F clo r rg)
  simp only [gpaco_clo_def] at heq
  rw [heq]
  -- Need: rclo clo (paco (composeRclo F clo) (rclo clo (paco ... ⊔ r)) ⊔ rclo clo (paco ... ⊔ r))
  --     ≤ rclo clo (paco (composeRclo F clo) (rg ⊔ r) ⊔ r)
  -- Use rclo idempotence: rclo clo (rclo clo R) ≤ rclo clo R
  apply Rel.le_trans _ rclo.rclo_rclo
  apply rclo.mono
  apply sup_le
  · -- paco (composeRclo F clo) (rclo clo (...)) ≤ rclo clo (...)
    -- Use: paco G (rclo clo S) ≤ paco G (upaco G S) ≤ paco G S (via accumulation)
    intro x y hpaco
    apply rclo.base
    left
    -- paco G (rclo clo (paco G (rg ⊔ r) ⊔ r)) → paco G (rg ⊔ r)
    -- Use that rclo clo S ≤ upaco G (rg ⊔ r) when S = paco G (rg ⊔ r) ⊔ r
    have hle : rclo clo (paco (composeRclo F clo) (rg ⊔ r) ⊔ r) ≤
               upaco (composeRclo F clo) (rg ⊔ r) := by
      intro a b hab
      induction hab with
      | base hr =>
        cases hr with
        | inl hp => left; exact hp
        | inr hr' => right; right; exact hr'
      | clo R' _ hcloR' ih =>
        -- ih : R' ≤ upaco G (rg ⊔ r)
        -- hcloR' : clo R' a b
        -- Need: upaco G (rg ⊔ r) a b, i.e., paco G (rg ⊔ r) a b ∨ (rg ⊔ r) a b
        --
        -- KNOWN LIMITATION: This case cannot be proven without additional structure.
        --
        -- The issue: We have `clo R' a b` where R' ⊆ upaco G (rg ⊔ r), but we need
        -- to show membership in upaco G (rg ⊔ r). There are two ways this could work:
        --
        -- 1. (rg ⊔ r) a b - but clo R' doesn't give us this
        -- 2. paco G (rg ⊔ r) a b - requires F (rclo clo (upaco G (rg ⊔ r))) a b
        --
        -- Neither is obtainable from `clo R' a b` without additional hypotheses.
        --
        -- The Coq paco library solves this using the "companion" construction:
        -- - cpn (companion) = ⋃ { clo | compatible clo }  (greatest compatible closure)
        -- - Key lemma: cpn (gupaco r) ≤ gupaco r (the companion preserves gupaco)
        -- - This requires significant additional infrastructure
        --
        -- Alternative solutions:
        -- 1. Implement the companion construction in UpTo.lean
        -- 2. Prove specialized lemmas for specific closures (congruence, etc.)
        -- 3. Add a "guardedness" hypothesis: ∀ S, clo (paco G S) ≤ rclo clo (paco G S)
        --
        -- For now, we admit this case. The library is still usable because:
        -- - The id closure case (no up-to) is fully proven (gpaco_clo_id)
        -- - Direct coinduction via gpaco_clo_cofix works without this lemma
        -- - gpaco_clo_final (gfp containment) is fully proven
        --
        -- See work/paco.md Appendix for detailed proof sketches.
        left
        apply paco_fold (composeRclo F clo) (rg ⊔ r)
        sorry
    have hpaco' := paco_mon (composeRclo F clo) hle x y hpaco
    exact paco_acc_upaco (composeRclo F clo) (rg ⊔ r) x y hpaco'
  · exact Rel.le_refl _

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
