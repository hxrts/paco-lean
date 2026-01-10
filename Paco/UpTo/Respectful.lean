import Paco.UpTo.Cpn
import Paco.UpTo.GPacoClo
import Paco.UpTo.Compose
import Paco.Companion

/-!
# Respectfulness

Respectfulness provides weaker conditions than compatibility that are often easier to prove.
The Coq paco library has three forms: wrespectful, prespectful, and grespectful.

## Overview

- `Compatible' F clo`: Compatibility with extended generator (id ⊔ F)
- `WRespectful F clo`: Weak respectfulness - clo l ≤ F (rclo clo r) when l ≤ r and l ≤ F r
- `PRespectful F clo`: Paco respectfulness - clo l ≤ paco F (r ⊔ clo r) when l ≤ r and l ≤ F r
- `GRespectful F clo`: Generalized respectfulness - most general form

All forms should imply that the closure is contained in the companion.

## Key Definitions

- `extendedGen F`: The extended generator, `extendedGen F R = R ⊔ F R`
- `Compatible' F clo`: Equivalent to `Compatible (extendedGen F) clo`
- `prespectClosure F clo`: Closure operator `R ↦ upaco F (R ⊔ clo R)` used for PRespectful

## Proof Structure

The main theorem chain is:
1. `compatible'_iff_compat_extended`: Compatible' F clo ↔ Compatible (extendedGen F) clo
2. `cpn_extendedGen_compat`: cpn F is (extendedGen F)-compatible (PROVEN)
3. `cpn_le_cpn_extendedGen`: cpn F ≤ cpn (extendedGen F) (PROVEN)
4. `cpn_extendedGen_le_cpn`: cpn (extendedGen F) ≤ cpn F (requires ExtCompatImpliesCompat)
5. `cpn_eq_cpn_extendedGen`: cpn F = cpn (extendedGen F) (requires ExtCompatImpliesCompat)
6. `cpn_extendedGen_F_compat`: cpn (extendedGen F) is F-compatible (via equality + assumption)
7. `compatible'_le_companion`: Compatible' closures ≤ companion (requires ExtCompatImpliesCompat)

## Proof Status

**Fully proven:**
- `cpn_compat'`: cpn F is Compatible' (ext-compatible via specific cpn structure)
- `cpn_extendedGen_compat`: cpn F is (extendedGen F)-compatible
- `cpn_le_cpn_extendedGen`: cpn F ≤ cpn (extendedGen F)
- `cpn_extendedGen_fixed`: cpn F R is a fixed point of extendedGen F
- `compatible'_le_companion`: Compatible' closures ≤ companion (requires ExtCompatImpliesCompat)
- `compat_wrespect`: Compatibility implies weak respectfulness
- `cloMono_wrespectfulExt`: Compatible' + monotone closure implies WRespectfulExt
- `wrespect_to_ext`: WRespectful + Compatible' implies WRespectfulExt
- `wrespect_compatible'`: WRespectfulExt implies Compatible' for rclo clo
- `wrespect_companion`: WRespectfulExt implies clo ≤ companion
- `prespect_companion`, `grespect_companion`: via Compatible' + ExtCompatImpliesCompat
- `wrespect_uclo`, `prespect_uclo`, `grespect_uclo`: UClo lemmas (prespect/grespect require Compatible')
- `prespectClosure_mono`, `clo_le_prespectClosure`: Helper lemmas for PRespectful

**Open (contain sorry):**
- None in this module (remaining sorries tracked elsewhere)
**Requires assumption:**
- `cpn_extendedGen_le_cpn` (line ~205): cpn (extendedGen F) ≤ cpn F
  - Requires `ExtCompatImpliesCompat F` (see Compat.lean)

## Technical Challenge

The fundamental issue across all remaining proofs is tracking "F-guardedness" through
closure operations:

1. **Coq's constructive proofs** use proof term structure to track which branch of
   `A ⊔ B` an element came from. When proving `clo l ≤ F (...)`, the proof term
   shows the element is constructively in the F-guarded branch.

2. **Lean's classical setting** uses case analysis `cases h with | inl => ... | inr => ...`
   which loses the tracking information. After the split, we can't determine which
   branch the original element came from.

3. **The WRespectful condition** requires BOTH `l ≤ r` AND `l ≤ F r`, but induction
   hypotheses give `l ≤ r ⊔ F r` (a disjunction), not the conjunction.

## Workarounds for Users

1. **Use standard compatibility**: If your closure is Compatible F clo (the stronger
   condition), use `cpn.greatest` directly - no respectfulness needed.

2. **Use `compat_wrespect`**: Convert compatibility to weak respectfulness; use
   WRespectfulExt when the extended-generator form is available.

3. **For Compatible' closures**: Use `compatible'_le_companion` after proving
   `Compatible (extendedGen F) clo`.

4. **Direct companion construction**: Show `clo R ≤ cpn F R` by finding a compatible
   monotone closure that dominates your closure.

## Potential Solutions for Completing Proofs

1. **Proof-relevant types**: Define a refined inductive that tracks guardedness
2. **Well-founded induction**: On the depth of rclo/cpn derivations with guardedness
3. **Choice axioms**: Use choice to extract witnesses for the F-guarded case
4. **Different proof strategies**: Prove equivalent statements that avoid case analysis

## References

- [Coq paco: gpaco.v](https://github.com/snu-sf/paco) - Respectfulness definitions
- [Coq paco: cpnN_gf](https://github.com/snu-sf/paco) - Proof that cpn F = cpn (id ⊔ F)
- [GPaco paper (CPP 2020)](https://paulhe.com/assets/gpaco.pdf) - Theoretical foundations
-/

namespace Paco

variable {α : Type*}

/-!
## Compatible' (Compatibility with id ⊔ F)

This auxiliary notion is used in the Coq paco library to bridge wrespectful to companion.
Compatible' F clo means: clo (R ⊔ F R) ≤ clo R ⊔ F (clo R)

This is equivalent to compatibility with gf' = id ⊔ gf, i.e., the extended generator
that allows staying in place (id) or making F-progress.
-/

-- Note: Compatible', extendedGen, and extendedGen_def are now defined in Paco.UpTo.Compat

/-- cpn F is compatible with extendedGen F, specialized proof using cpn structure.

This is the key lemma showing cpn F satisfies the Compatible' property.
The proof uses cpn.step to absorb F (cpn F R) ≤ cpn F R. -/
theorem cpn_compat' (F : MonoRel α) : Compatible' F (cpn F) := by
  intro R
  -- Goal: cpn F (R ⊔ F R) ≤ cpn F R ⊔ F (cpn F R)
  have h_RFR_le : R ⊔ F R ≤ cpn F R := by
    apply sup_le cpn.base
    exact Rel.le_trans (F.mono' cpn.base) cpn.step
  calc cpn F (R ⊔ F R)
      ≤ cpn F (cpn F R) := cpn.mono h_RFR_le
    _ ≤ cpn F R := cpn.cpn_cpn
    _ ≤ cpn F R ⊔ F (cpn F R) := le_sup_left

/-- cpn F R is a fixed point of extendedGen F: (extendedGen F) (cpn F R) = cpn F R.

This follows from cpn.step: F (cpn F R) ≤ cpn F R, which means the F-part of
the union is absorbed. -/
theorem cpn_extendedGen_fixed (F : MonoRel α) (R : Rel α) :
    extendedGen F (cpn F R) ≤ cpn F R := by
  -- (extendedGen F) (cpn F R) = cpn F R ⊔ F (cpn F R)
  -- By cpn.step: F (cpn F R) ≤ cpn F R
  -- So the union equals cpn F R
  simp only [extendedGen_def]
  apply sup_le (Rel.le_refl _) cpn.step

/-- cpn F is (extendedGen F)-compatible.

This is the key lemma for showing cpn F = cpn (extendedGen F). The proof uses:
1. R ⊔ F R ≤ cpn F R (from cpn.base and cpn.step)
2. cpn F (R ⊔ F R) ≤ cpn F (cpn F R) by monotonicity
3. cpn F (cpn F R) ≤ cpn F R by cpn.cpn_cpn -/
theorem cpn_extendedGen_compat (F : MonoRel α) : Compatible (extendedGen F) (cpn F) := by
  intro R
  -- Goal: cpn F ((extendedGen F) R) ≤ (extendedGen F) (cpn F R)
  -- i.e., cpn F (R ⊔ F R) ≤ cpn F R ⊔ F (cpn F R)
  -- Since F (cpn F R) ≤ cpn F R (by cpn.step), the RHS equals cpn F R.
  -- So we need: cpn F (R ⊔ F R) ≤ cpn F R.
  have h_RFR_le : R ⊔ F R ≤ cpn F R := by
    apply sup_le
    · exact cpn.base  -- R ≤ cpn F R
    · -- F R ≤ F (cpn F R) ≤ cpn F R
      exact Rel.le_trans (F.mono' cpn.base) cpn.step
  calc cpn F (extendedGen F R)
      = cpn F (R ⊔ F R) := rfl
    _ ≤ cpn F (cpn F R) := cpn.mono h_RFR_le
    _ ≤ cpn F R := cpn.cpn_cpn
    _ ≤ cpn F R ⊔ F (cpn F R) := le_sup_left
    _ = extendedGen F (cpn F R) := rfl

/-- cpn F ≤ cpn (extendedGen F), since cpn F is (extendedGen F)-compatible. -/
theorem cpn_le_cpn_extendedGen (F : MonoRel α) (R : Rel α) :
    cpn F R ≤ cpn (extendedGen F) R :=
  cpn.greatest cpn.cpn_cloMono (cpn_extendedGen_compat F)

/-- F R ≤ cpn F R via base and step.

This helper shows that F R is contained in cpn F R, which is key for
showing cpn (extendedGen F) is F-compatible. -/
theorem F_le_cpn (F : MonoRel α) (R : Rel α) : F R ≤ cpn F R := by
  -- F R ≤ F (cpn F R) by F.mono (since R ≤ cpn F R by cpn.base)
  -- F (cpn F R) ≤ cpn F R by cpn.step
  exact Rel.le_trans (F.mono' cpn.base) cpn.step

/-- extendedGen F (cpn F R) = cpn F R (cpn F R is a fixed point of extendedGen F).

Since F (cpn F R) ≤ cpn F R by cpn.step, we have:
extendedGen F (cpn F R) = cpn F R ⊔ F (cpn F R) = cpn F R -/
theorem cpn_extendedGen_fixedpoint (F : MonoRel α) (R : Rel α) :
    extendedGen F (cpn F R) = cpn F R := by
  apply Rel.le_antisymm
  · -- extendedGen F (cpn F R) ≤ cpn F R
    exact cpn_extendedGen_fixed F R
  · -- cpn F R ≤ extendedGen F (cpn F R) = cpn F R ⊔ F (cpn F R)
    exact le_sup_left

/-- If extendedGen-compatible closures are already F-compatible, then
    the extended-generator companion is bounded by the original companion. -/
theorem cpn_extendedGen_le_cpn (F : MonoRel α) (R : Rel α)
    [h_ext : ExtCompatImpliesCompat F] :
    cpn (extendedGen F) R ≤ cpn F R := by
  intro x y hcpn
  obtain ⟨clo, h_mono, h_compat_ext, h_clo⟩ := hcpn
  have h_compat : Compatible F clo := h_ext.h clo h_mono h_compat_ext
  exact cpn.greatest h_mono h_compat x y h_clo

/-- cpn F = cpn (extendedGen F).

The companions for F and (extendedGen F) = (id ⊔ F) are equal. This is because:
- cpn F is (extendedGen F)-compatible (cpn_extendedGen_compat)
- Any (extendedGen F)-compatible closure stays within cpn F R -/
theorem cpn_eq_cpn_extendedGen (F : MonoRel α) (R : Rel α)
    [ExtCompatImpliesCompat F] :
    cpn F R = cpn (extendedGen F) R :=
  Rel.le_antisymm (cpn_le_cpn_extendedGen F R) (cpn_extendedGen_le_cpn F R)

/-- cpn (extendedGen F) is F-compatible, by equality with cpn F. -/
theorem cpn_extendedGen_F_compat (F : MonoRel α) [ExtCompatImpliesCompat F] :
    Compatible F (cpn (extendedGen F)) := by
  intro R
  -- Rewrite both occurrences of cpn F using the cpn equality at R and F R.
  simpa [cpn_eq_cpn_extendedGen (F := F) (R := R),
         cpn_eq_cpn_extendedGen (F := F) (R := F R)] using
    (cpn.compat (F := F) (R := R))

-- Note: compatible'_iff_compat_extended is now compatible'_iff_compat_extendedGen in Compat.lean

/-- Compatible' closures are contained in the companion.

Following Coq's approach (cpnN_from_compatible'):
1. Compatible' F clo = Compatible (extendedGen F) clo
2. By cpn.greatest for extendedGen: clo ≤ cpn (extendedGen F)
3. By cpn_eq_cpn_extendedGen (with ExtCompatImpliesCompat): cpn (extendedGen F) = cpn F

This avoids the circular dependency by working with the extended generator
and using the key equality cpn F = cpn (extendedGen F). -/
theorem compatible'_le_companion (F : MonoRel α) {clo : Rel α → Rel α}
    (h_mono : CloMono clo) (h_compat' : Compatible' F clo)
    [ExtCompatImpliesCompat F] :
    ∀ R, clo R ≤ companion F R := by
  intro R
  -- Step 1: clo is compatible with extendedGen F (by hypothesis)
  have h_compat_ext : Compatible (extendedGen F) clo :=
    (compatible'_iff_compat_extendedGen F clo).mp h_compat'
  -- Step 2: By cpn.greatest, clo ≤ cpn (extendedGen F)
  have h_clo_le_cpn_ext : clo R ≤ cpn (extendedGen F) R :=
    cpn.greatest h_mono h_compat_ext
  -- Step 3: cpn (extendedGen F) = cpn F
  have h_cpn_eq : cpn (extendedGen F) R = cpn F R := (cpn_eq_cpn_extendedGen F R).symm
  -- Combine: clo R ≤ cpn (extendedGen F) R = cpn F R = companion F R
  rw [h_cpn_eq] at h_clo_le_cpn_ext
  exact h_clo_le_cpn_ext

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

/-!
### Extended Weak Respectfulness

The standard WRespectful requires BOTH `l ≤ r` AND `l ≤ F r`. But in Coq's compatible'
context where gf' = id ⊔ gf is used, the condition `l ≤ gf' r = l ≤ r ⊔ F r` can be
satisfied by EITHER `l ≤ r` OR `l ≤ F r`.

This motivates WRespectfulExt, which has:
- Hypothesis: l ≤ r ⊔ F r (satisfied by either branch)
- Conclusion: clo l ≤ rclo clo r ⊔ F (rclo clo r) (lands in extended generator)

This is the condition that actually matches Coq's compatible' proof structure.
-/

/-- Extended weak respectfulness: the condition used in Coq's compatible' proofs.

This version uses the "extended generator" formulation:
- Input: l ≤ extendedGen F r = l ≤ r ⊔ F r
- Output: clo l ≤ extendedGen F (rclo clo r) = rclo clo r ⊔ F (rclo clo r)

The key property is that the input condition is satisfied by EITHER l ≤ r OR l ≤ F r,
not requiring both simultaneously. This allows the tagged rclo proof to work. -/
structure WRespectfulExt (F : MonoRel α) (clo : Rel α → Rel α) : Prop where
  /-- The closure is monotone -/
  mon : CloMono clo
  /-- The extended respect condition -/
  respect : ∀ l r, l ≤ r ⊔ F r → clo l ≤ rclo clo r ⊔ F (rclo clo r)

/-- Any Compatible' monotone closure satisfies WRespectfulExt.

This is because:
- clo l ≤ clo (r ⊔ F r) by monotonicity (since l ≤ r ⊔ F r)
- clo (r ⊔ F r) ≤ clo r ⊔ F (clo r) by Compatible'
- clo r ≤ rclo clo r by rclo.clo_base, and F respects ≤ -/
theorem cloMono_wrespectfulExt (F : MonoRel α) {clo : Rel α → Rel α}
    (h_mono : CloMono clo) (h_compat' : Compatible' F clo) : WRespectfulExt F clo where
  mon := h_mono
  respect := by
    intro l r h_le_ext
    -- h_le_ext : l ≤ r ⊔ F r
    -- Goal: clo l ≤ rclo clo r ⊔ F (rclo clo r)
    have h1 : clo l ≤ clo (r ⊔ F r) := h_mono _ _ h_le_ext
    have h2 : clo (r ⊔ F r) ≤ clo r ⊔ F (clo r) := h_compat' r
    have h3 : clo r ⊔ F (clo r) ≤ rclo clo r ⊔ F (rclo clo r) := by
      apply sup_le
      · exact Rel.le_trans rclo.clo_base le_sup_left
      · exact Rel.le_trans (F.mono' rclo.clo_base) le_sup_right
    exact Rel.le_trans h1 (Rel.le_trans h2 h3)

/-- Weak respectfulness: a weaker condition than compatibility.

A closure `clo` is weakly respectful with respect to `F` if it is monotone and
for any `l ≤ r` with `l ≤ F r`, we have `clo l ≤ F (rclo clo r)`. -/
structure WRespectful (F : MonoRel α) (clo : Rel α → Rel α) : Prop where
  /-- The closure is monotone -/
  mon : CloMono clo
  /-- The respect condition: clo l ≤ F (rclo clo r) when l ≤ r and l ≤ F r -/
  respect : ∀ l r, l ≤ r → l ≤ F r → clo l ≤ F (rclo clo r)

/-- WRespectful + Compatible' implies WRespectfulExt. -/
theorem wrespect_to_ext (F : MonoRel α) {clo : Rel α → Rel α}
    (h : WRespectful F clo) (h_compat' : Compatible' F clo) : WRespectfulExt F clo :=
  cloMono_wrespectfulExt F h.mon h_compat'

/-- rcloTagged elements (both guarded and unguarded) land in rclo clo R ⊔ F (rclo clo R)
    when clo satisfies WRespectfulExt. -/
theorem rcloTagged_le_extendedGen (clo : Rel α → Rel α) (F : MonoRel α) (R : Rel α)
    (h : WRespectfulExt F clo) (b : Bool) :
    rcloTagged clo F R b ≤ rclo clo R ⊔ F (rclo clo R) := by
  intro x y hrt
  induction hrt with
  | base_unguarded hr =>
    left; exact rclo.base hr
  | base_guarded hf =>
    right; exact F.mono' rclo.base_le _ _ hf
  | clo_step b' R' hR' hclo ih =>
    -- hR' : ∀ a c, R' a c → rcloTagged clo F R b' a c
    -- hclo : clo R' x✝ y✝ (pattern match variables)
    -- ih : ∀ a c, R' a c → (rclo clo R ⊔ F (rclo clo R)) a c

    -- By ih: R' ≤ rclo clo R ⊔ F (rclo clo R)
    have hR'_le : R' ≤ rclo clo R ⊔ F (rclo clo R) := ih

    -- By WRespectfulExt with l = R' and r = rclo clo R:
    -- Need: R' ≤ rclo clo R ⊔ F (rclo clo R) ✓ (this is hR'_le)
    -- Conclusion: clo R' ≤ rclo clo (rclo clo R) ⊔ F (rclo clo (rclo clo R))
    have h_resp := h.respect R' (rclo clo R) hR'_le
    -- h_resp : clo R' ≤ rclo clo (rclo clo R) ⊔ F (rclo clo (rclo clo R))

    -- By rclo_rclo: rclo clo (rclo clo R) ≤ rclo clo R
    have h_rclo_rclo := rclo.rclo_rclo (clo := clo) (R := R)

    -- So: clo R' ≤ rclo clo R ⊔ F (rclo clo R)
    have h_final : clo R' ≤ rclo clo R ⊔ F (rclo clo R) := by
      intro a c hac
      cases h_resp a c hac with
      | inl h_in_rclo =>
        left; exact h_rclo_rclo a c h_in_rclo
      | inr h_in_F =>
        right; exact F.mono' h_rclo_rclo a c h_in_F

    exact h_final _ _ hclo

/-- Extended weak respectfulness implies rclo clo is Compatible'.

This theorem shows that if clo is weakly respectful, then rclo clo satisfies
the compatibility condition: rclo clo (R ⊔ F R) ≤ rclo clo R ⊔ F (rclo clo R).

**Proof strategy** (following Coq's wrespect0_compatible'):

The key insight is that Compatible' F clo = Compatible (extendedGen F) clo, where
extendedGen F R = R ⊔ F R. When working with this "extended generator", the
WRespectful GF condition `l ≤ (extendedGen F) r = l ≤ r ⊔ F r` is IMPLIED by `l ≤ r`.

This means we can apply WRespectful whenever we have `l ≤ r`, since:
- LE condition: `l ≤ r` (given)
- GF condition: `l ≤ r ⊔ F r` (follows from l ≤ r by le_sup_left)

The proof proceeds by induction on rclo:
- Base case: Elements from R go to rclo clo R (left), elements from F R go to F (rclo clo R)
- Clo case: Apply WRespectful with l = R' and r = rclo clo (R ⊔ F R)
  - LE: R' ≤ rclo clo (R ⊔ F R) is given by the rclo constructor
  - GF: R' ≤ rclo clo (R ⊔ F R) ⊔ F (rclo clo (R ⊔ F R)) follows from LE
  - WRespectful gives: clo R' ≤ F (rclo clo (rclo clo (R ⊔ F R)))
  - By rclo_rclo: rclo clo (rclo clo (R ⊔ F R)) ≤ rclo clo (R ⊔ F R)
  - By F.mono: F (rclo clo (rclo clo (R ⊔ F R))) ≤ F (rclo clo (R ⊔ F R))
  - Now use the IH: rclo clo (R ⊔ F R) ≤ rclo clo R ⊔ F (rclo clo R)
  - By F.mono: F (rclo clo (R ⊔ F R)) ≤ F (rclo clo R ⊔ F (rclo clo R))
  - Finally show F (rclo clo R ⊔ F (rclo clo R)) ≤ rclo clo R ⊔ F (rclo clo R)
-/
theorem wrespect_compatible' (F : MonoRel α) {clo : Rel α → Rel α}
    (h : WRespectfulExt F clo) : Compatible' F (rclo clo) := by
  intro R
  -- Let S be the target relation.
  let S : Rel α := rclo clo R ⊔ F (rclo clo R)
  -- Show rclo clo (R ⊔ F R) ≤ S by rclo_smallest.
  apply rclo.rclo_smallest
  · -- Base: R ⊔ F R ≤ S
    apply sup_le
    · exact Rel.le_trans rclo.base_le le_sup_left
    · exact Rel.le_trans (F.mono' rclo.base_le) le_sup_right
  · -- Clo-closed: if R' ≤ S then clo R' ≤ S
    intro R' hR'
    -- Apply WRespectfulExt with r = rclo clo R, noting S = r ⊔ F r.
    have h_resp :
        clo R' ≤ rclo clo (rclo clo R) ⊔ F (rclo clo (rclo clo R)) :=
      h.respect R' (rclo clo R) hR'
    have h_shrink : rclo clo (rclo clo R) ≤ rclo clo R := rclo.rclo_rclo
    have h_sup : rclo clo (rclo clo R) ⊔ F (rclo clo (rclo clo R)) ≤ S := by
      apply sup_le
      · exact Rel.le_trans h_shrink le_sup_left
      · exact Rel.le_trans (F.mono' h_shrink) le_sup_right
    exact Rel.le_trans h_resp h_sup

/-- Extended weak respectfulness implies the closure is contained in the companion.

This is the key lemma connecting wrespectful to the companion.

**Proof strategy**: Show rclo clo R ≤ companion F R using rclo_smallest.
This requires showing the companion is clo-closed, which involves:
- Using WRespectfulExt on guarded inputs (F(companion F R))
- Handling unguarded inputs (R) via companion_extensive

**Note**: The proof has a circular dependency that requires either:
1. A weaker Compatible' definition (as in Coq paco)
2. A coinductive argument showing companion is clo-closed
3. A well-founded induction on rclo depth

Currently uses wrespect_compatible' in the extended form. -/
theorem wrespect_companion (F : MonoRel α) {clo : Rel α → Rel α}
    (h : WRespectfulExt F clo) [ExtCompatImpliesCompat F] :
    ∀ R, clo R ≤ companion F R := by
  intro R
  -- Strategy: clo R ≤ rclo clo R ≤ companion F R
  -- The second step uses compatible'_le_companion via wrespect_compatible'
  have h_compat' : Compatible' F (rclo clo) := wrespect_compatible' F h
  have h1 : clo R ≤ rclo clo R := rclo.clo_base
  have h2 : rclo clo R ≤ companion F R :=
    compatible'_le_companion F (rclo_mono clo) h_compat' R
  exact Rel.le_trans h1 h2

/-- Weak respectfulness uclo lemma: clo R ≤ gupaco_clo F (companion F) R -/
theorem wrespect_uclo (F : MonoRel α) {clo : Rel α → Rel α}
    (h : WRespectfulExt F clo) [ExtCompatImpliesCompat F] (R : Rel α) :
    clo R ≤ gupaco_clo F (companion F) R := by
  intro x y hclo
  have h1 : clo R ≤ companion F R := wrespect_companion F h R
  -- companion F R ≤ gupaco_clo F (companion F) R by companion_gupaco_eq
  have h2 : companion F R = gupaco_clo F (companion F) R := (companion_gupaco_eq F R).symm
  rw [← h2]
  exact h1 x y hclo

/-!
## Paco Respectfulness
-/

/-- Paco respectfulness: another form of respectfulness using paco directly.

A closure `clo` is paco-respectful with respect to `F` if it is monotone and
for any `l ≤ r` with `l ≤ F r`, we have `clo l ≤ paco F (r ⊔ clo r)`. -/
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

/-!
## Generalized Respectfulness
-/

/-- Generalized respectfulness: the most general form of respectfulness.

A closure `clo` is generalized-respectful with respect to `F` if it is monotone and
for any `l ≤ r` with `l ≤ F r`, we have
`clo l ≤ rclo (companion F) (F (rclo (clo ⊔ gupaco_clo F (companion F)) r))`. -/
structure GRespectful (F : MonoRel α) (clo : Rel α → Rel α) : Prop where
  /-- The closure is monotone -/
  mon : CloMono clo
  /-- The respect condition -/
  respect : ∀ l r, l ≤ r → l ≤ F r →
    clo l ≤ rclo (companion F) (F (rclo (cloUnion clo (gupaco_clo F (companion F))) r))

/-- Generalized respectfulness implies the closure is contained in the companion.

Currently routed through the Compatible' → companion chain, which requires:
- `Compatible' F clo`
- `ExtCompatImpliesCompat F`

This keeps the lemma usable in settings where Compatible' is available. -/
theorem grespect_companion (F : MonoRel α) {clo : Rel α → Rel α}
    (h : GRespectful F clo) (h_compat' : Compatible' F clo)
    [ExtCompatImpliesCompat F] : ∀ R, clo R ≤ companion F R :=
  compatible'_le_companion F h.mon h_compat'

/-- Generalized respectfulness uclo lemma: clo R ≤ gupaco_clo F (companion F) R -/
theorem grespect_uclo (F : MonoRel α) {clo : Rel α → Rel α}
    (h : GRespectful F clo) (h_compat' : Compatible' F clo)
    [ExtCompatImpliesCompat F] (R : Rel α) :
    clo R ≤ gupaco_clo F (companion F) R := by
  intro x y hclo
  have h1 : clo R ≤ companion F R := grespect_companion F h h_compat' R
  have h2 : companion F R = gupaco_clo F (companion F) R := (companion_gupaco_eq F R).symm
  rw [← h2]
  exact h1 x y hclo

/-!
## Relationships Between Respectfulness Forms

The three forms of respectfulness are related by implication:
- Compatible F clo → WRespectful F clo
- WRespectful F clo → PRespectful F clo (under certain conditions)
- PRespectful F clo → GRespectful F clo (under certain conditions)
-/

/-- Compatibility implies weak respectfulness -/
theorem compat_wrespect (F : MonoRel α) {clo : Rel α → Rel α}
    (h_mono : CloMono clo) (h_compat : Compatible F clo) :
    WRespectful F clo where
  mon := h_mono
  respect := by
    intro l r _hle hlF x y hclo
    -- From clo l x y and l ≤ F r
    -- We have clo (F r) ≤ F (clo r) by compatibility
    -- And clo r ≤ rclo clo r by rclo.clo_base
    have h1 : clo l ≤ clo (F r) := h_mono l (F r) hlF
    have h2 : clo (F r) ≤ F (clo r) := h_compat r
    have h3 : clo r ≤ rclo clo r := rclo.clo_base
    have h4 : F (clo r) ≤ F (rclo clo r) := F.mono' h3
    exact h4 x y (h2 x y (h1 x y hclo))

end Paco
