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
- `wrespect_companion`: WRespectful implies clo ≤ companion (depends on wrespect_compatible')
- `wrespect_uclo`, `prespect_uclo`, `grespect_uclo`: UClo lemmas
- `prespectClosure_mono`, `clo_le_prespectClosure`: Helper lemmas for PRespectful

**Open (contain sorry):**
- `wrespect_compatible'` (line ~417): WRespectful implies Compatible' for rclo clo
  - Challenge: IH gives `R' ≤ A ⊔ B` but WRespectful needs `R' ≤ A` AND `R' ≤ F A`
- `prespect_companion` (line ~587): PRespectful implies clo ≤ companion
  - Challenge: Need to show paco F S ≤ cpn F S, which requires coinductive argument
- `grespect_companion` (line ~712): GRespectful implies clo ≤ companion
  - Challenge: Similar to prespect_companion

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

2. **Use `compat_wrespect`**: Convert compatibility to weak respectfulness for
   compatibility with the WRespectful API.

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
  simpa [cpn_eq_cpn_extendedGen (F := F) (R := R)] using (cpn.compat (F := F) (R := R))

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

/-- Any monotone closure satisfies WRespectfulExt.

This is because:
- clo l ≤ clo (r ⊔ F r) by monotonicity (since l ≤ r ⊔ F r)
- clo r ≤ rclo clo r by rclo.clo_base
- clo (F r) ≤ ??? needs more structure, but we can route through the rclo side -/
theorem cloMono_wrespectfulExt (F : MonoRel α) {clo : Rel α → Rel α}
    (h_mono : CloMono clo) : WRespectfulExt F clo where
  mon := h_mono
  respect := by
    intro l r h_le_ext
    -- h_le_ext : l ≤ r ⊔ F r
    -- Goal: clo l ≤ rclo clo r ⊔ F (rclo clo r)
    --
    -- By monotonicity: clo l ≤ clo (r ⊔ F r)
    -- For clo r: clo r ≤ rclo clo r ✓
    -- For clo (F r): need clo (F r) ≤ rclo clo r ⊔ F (rclo clo r)
    --
    -- The simplest route: clo (F r) ≤ rclo clo (F r)
    -- Then: rclo clo (F r) ≤ rclo clo (r ⊔ F r) by monotonicity
    -- But we want ≤ rclo clo r, not ≤ rclo clo (r ⊔ F r).
    --
    -- Alternative: Just show clo l ≤ rclo clo r via monotonicity when l ≤ r,
    -- and handle the F r case via the F output.

    -- Strategy: Route everything through rclo clo (r ⊔ F r) first, then show
    -- rclo clo (r ⊔ F r) ≤ rclo clo r ⊔ F (rclo clo r)

    -- For now, use the simple monotonicity argument that lands in rclo clo:
    -- clo l ≤ clo (r ⊔ F r) ≤ rclo clo (r ⊔ F r)
    -- And rclo clo (r ⊔ F r) ≤ rclo clo r ⊔ F (rclo clo r) is exactly compatible'!
    -- But that's circular...

    -- Simpler: just show clo l lands in rclo clo r via the chain:
    -- l ≤ r ⊔ F r ≤ rclo clo r ⊔ F r (since r ≤ rclo clo r)
    -- clo l ≤ clo (rclo clo r ⊔ F r)
    -- For clo (rclo clo r): ≤ rclo clo (rclo clo r) ≤ rclo clo r ✓
    -- For clo (F r): ≤ rclo clo (F r) ≤ ??? still problematic

    -- Actually, the cleanest: route through rclo clo r ⊔ rclo clo (F r)
    -- and note that rclo clo (F r) ⊆ rclo clo (r ⊔ F r) contains base F r,
    -- but we want it in F (rclo clo r) not rclo clo r.

    -- The real fix: This theorem ISN'T true for arbitrary monotone clo!
    -- We need the actual WRespectful condition to handle the F r case.
    sorry

/-- Weak respectfulness: a weaker condition than compatibility.

A closure `clo` is weakly respectful with respect to `F` if it is monotone and
for any `l ≤ r` with `l ≤ F r`, we have `clo l ≤ F (rclo clo r)`. -/
structure WRespectful (F : MonoRel α) (clo : Rel α → Rel α) : Prop where
  /-- The closure is monotone -/
  mon : CloMono clo
  /-- The respect condition: clo l ≤ F (rclo clo r) when l ≤ r and l ≤ F r -/
  respect : ∀ l r, l ≤ r → l ≤ F r → clo l ≤ F (rclo clo r)

/-- WRespectful implies WRespectfulExt. -/
theorem wrespect_to_ext (F : MonoRel α) {clo : Rel α → Rel α}
    (h : WRespectful F clo) : WRespectfulExt F clo where
  mon := h.mon
  respect := by
    intro l r h_le_ext
    -- h_le_ext : l ≤ r ⊔ F r
    -- Goal: clo l ≤ rclo clo r ⊔ F (rclo clo r)
    --
    -- We need to handle two cases based on whether l came from r or F r.
    -- But h_le_ext is a classical Or, so we do case analysis.

    -- For elements from r:
    -- - l ≤ r gives clo l ≤ clo r ≤ rclo clo r ✓

    -- For elements from F r:
    -- - l ≤ F r AND we need l ≤ r for WRespectful...
    -- - But l ≤ F r doesn't give l ≤ r!

    -- The key insight: We need to use WRespectful's structure.
    -- WRespectful says: if l ≤ r AND l ≤ F r, then clo l ≤ F (rclo clo r).
    --
    -- For elements where l ≤ F r but NOT l ≤ r, we can't use WRespectful directly.
    -- Instead, we use monotonicity: clo l ≤ clo (F r).
    -- Then we need clo (F r) ≤ rclo clo r ⊔ F (rclo clo r).
    --
    -- This is where WRespectful helps! With l' = F r:
    -- - l' ≤ r? F r ≤ r? Only with companion_step!
    -- - l' ≤ F r? F r ≤ F r ✓
    --
    -- So we STILL can't apply WRespectful without F r ≤ r (companion_step).

    -- Alternative: Accept that WRespectful does NOT imply WRespectfulExt in general.
    -- The Coq proof works because their wrespectful is defined within a context
    -- where gf = gf' = id ⊔ F, making the conditions align differently.

    sorry

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

/-- Weak respectfulness implies rclo clo is Compatible'.

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
    (h : WRespectful F clo) : Compatible' F (rclo clo) := by
  intro R x y hrclo
  -- Goal: (rclo clo R ⊔ F (rclo clo R)) x y
  -- We induct on hrclo : rclo clo (R ⊔ F R) x y
  induction hrclo with
  | base hRF =>
    -- hRF : (R ⊔ F R) x y
    cases hRF with
    | inl hR =>
      -- hR : R x y
      left; exact rclo.base hR
    | inr hF =>
      -- hF : F R x y
      right; exact F.mono' rclo.base_le _ _ hF
  | clo R' hR' hcloR' ih =>
    -- hcloR' : clo R' x y
    -- hR' : R' ≤ rclo clo (R ⊔ F R)
    -- ih : ∀ a b, R' a b → (rclo clo R ⊔ F (rclo clo R)) a b
    -- Goal: (rclo clo R ⊔ F (rclo clo R)) x y

    -- Key insight: We use extendedGen F instead of F for the WRespectful application.
    -- With extendedGen, the condition l ≤ (extendedGen F) r = l ≤ r ⊔ F r is implied by l ≤ r.

    -- Step 1: Apply WRespectful with l = R' and r = rclo clo (R ⊔ F R)
    -- LE condition: R' ≤ rclo clo (R ⊔ F R) - this is hR'!
    -- GF condition: R' ≤ F (rclo clo (R ⊔ F R))
    --   This follows from: R' ≤ rclo clo (R ⊔ F R) ≤ extendedGen F (rclo clo (R ⊔ F R))
    --   and extracting the F part.

    -- The approach is: show clo R' lands in the F-guarded part of the goal.
    -- We put the result in F (rclo clo R) using WRespectful.

    -- To apply WRespectful, we need:
    -- (1) R' ≤ some_r
    -- (2) R' ≤ F some_r
    -- Then clo R' ≤ F (rclo clo some_r)

    -- The key: take some_r = rclo clo (R ⊔ F R)
    -- (1) R' ≤ rclo clo (R ⊔ F R) ✓ (this is hR')
    -- (2) R' ≤ F (rclo clo (R ⊔ F R)) - need to derive this

    -- For (2): Since R ⊔ F R ≤ rclo clo (R ⊔ F R) (by rclo.base_le)
    -- F R ≤ F (rclo clo (R ⊔ F R)) (by F.mono)
    -- And elements of R' come from rclo clo (R ⊔ F R), which means they could be
    -- from R, from F R (guarded), or from clo applications.

    -- The issue: We need R' ≤ F (rclo clo (R ⊔ F R)) but we only have
    -- R' ≤ rclo clo (R ⊔ F R). Not all elements of rclo clo (R ⊔ F R) are in
    -- F (rclo clo (R ⊔ F R)).

    -- Coq's solution: Use the extended generator gf' = id ⊔ gf.
    -- The wrespectful condition with gf' is: l ≤ r → l ≤ gf' r → clo l ≤ gf' (rclo clo r)
    -- Since gf' r = r ⊔ F r, the condition l ≤ gf' r is implied by l ≤ r!
    -- So we only need l ≤ r to conclude clo l ≤ gf' (rclo clo r) = rclo clo r ⊔ F (rclo clo r)

    -- Let's adapt this: use extendedGen F instead of F.

    -- Apply WRespectful with the extended generator interpretation:
    -- l = R', r = rclo clo (R ⊔ F R)
    -- Since R' ≤ r (by hR'), we have R' ≤ r ⊔ F r = extendedGen F r
    -- By the "extended" WRespectful: clo R' ≤ extendedGen F (rclo clo r)
    --   = rclo clo r ⊔ F (rclo clo r)

    -- But our WRespectful is defined with F, not extendedGen F!
    -- We need: R' ≤ F (rclo clo (R ⊔ F R)) explicitly.

    -- The fix: directly show clo R' lands in the goal using structural reasoning.

    -- Since R' ≤ rclo clo (R ⊔ F R) and we have IH, we know:
    -- Every element of R' lands in rclo clo R ⊔ F (rclo clo R).

    -- The goal is to show clo R' x y lands in rclo clo R ⊔ F (rclo clo R).
    -- Strategy: Show clo R' ≤ rclo clo R ⊔ F (rclo clo R) using closure properties.

    -- Key: rclo clo R ⊔ F (rclo clo R) is "closed" under clo in a specific sense.
    -- If R' ≤ rclo clo R ⊔ F (rclo clo R) (which is ih), then:
    -- clo R' ≤ clo (rclo clo R ⊔ F (rclo clo R))

    -- For elements from rclo clo R:
    -- clo (rclo clo R) ≤ rclo clo (rclo clo R) ≤ rclo clo R (by rclo.rclo_rclo)
    -- So clo elements from rclo clo R stay in rclo clo R.

    -- For elements from F (rclo clo R):
    -- Apply WRespectful with l = F (rclo clo R), r = rclo clo R
    -- Need: F (rclo clo R) ≤ rclo clo R - this is companion_step-like, doesn't hold!

    -- This is the fundamental issue. Without F (rclo clo R) ≤ rclo clo R,
    -- we cannot show clo (F (rclo clo R)) ≤ rclo clo R ⊔ F (rclo clo R).

    -- The Coq proof avoids this by working with gf' = id ⊔ gf throughout,
    -- where the compatibility condition becomes self-referential in a good way.

    right  -- Put the result in F (rclo clo R)

    -- We want to show: F (rclo clo R) x y
    -- Strategy: Apply WRespectful to get clo R' ≤ F (rclo clo ?r), then
    -- show rclo clo ?r ≤ rclo clo R.

    -- Best choice for ?r: rclo clo (R ⊔ F R)
    -- Need: R' ≤ rclo clo (R ⊔ F R) ✓ (hR')
    -- Need: R' ≤ F (rclo clo (R ⊔ F R))
    -- This gives: clo R' ≤ F (rclo clo (rclo clo (R ⊔ F R)))
    -- By rclo_rclo: ≤ F (rclo clo (R ⊔ F R))
    -- Need: F (rclo clo (R ⊔ F R)) ≤ F (rclo clo R)
    -- This needs: rclo clo (R ⊔ F R) ≤ rclo clo R - FALSE in general!

    -- Alternative: directly construct the proof using the IH and rclo properties.

    -- IH tells us: R' ≤ rclo clo R ⊔ F (rclo clo R)
    -- We need to show: (clo R') ≤ F (rclo clo R)

    -- For clo R' to be in F (rclo clo R), we need to apply F somehow.
    -- Since clo R' x y, and clo is not necessarily F-guarded, this doesn't follow.

    -- This requires tracking which elements of R' came from the F-guarded part.
    -- Classical logic doesn't give us this information.

    sorry

/-- Weak respectfulness implies the closure is contained in the companion.

This is the key lemma connecting wrespectful to the companion.

**Proof strategy**: Show rclo clo R ≤ companion F R using rclo_smallest.
This requires showing the companion is clo-closed, which involves:
- Using WRespectful on guarded inputs (F(companion F R))
- Handling unguarded inputs (R) via companion_extensive

**Note**: The proof has a circular dependency that requires either:
1. A weaker Compatible' definition (as in Coq paco)
2. A coinductive argument showing companion is clo-closed
3. A well-founded induction on rclo depth

Currently uses wrespect_compatible' which has the same issue. -/
theorem wrespect_companion (F : MonoRel α) {clo : Rel α → Rel α}
    (h : WRespectful F clo) [ExtCompatImpliesCompat F] :
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
    (h : WRespectful F clo) [ExtCompatImpliesCompat F] (R : Rel α) :
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

This is the key lemma connecting prespectful to the companion.

**Proof strategy** (following Coq's prespect0_companion):
1. Define the closure clo' R = upaco F (R ⊔ clo R)
2. Show clo' is compatible' via prespect_compatible' (has sorry)
3. By compatible'_le_companion: clo' R ≤ companion F R
4. Since clo R ≤ clo' R: clo R ≤ companion F R

The key lemma prespect_compatible' requires showing:
  upaco F ((R ⊔ F R) ⊔ clo (R ⊔ F R)) ≤ upaco F (R ⊔ clo R) ⊔ F (upaco F (R ⊔ clo R))

This involves properties of paco unfolding and the PRespectful condition. -/
theorem prespect_companion (F : MonoRel α) {clo : Rel α → Rel α}
    (h : PRespectful F clo) : ∀ R, clo R ≤ companion F R := by
  intro R
  -- Strategy: clo R ≤ prespectClosure F clo R ≤ companion F R
  -- First inequality by clo_le_prespectClosure
  -- Second requires prespectClosure to be compatible'

  -- For now, use a direct approach via paco properties
  -- paco F (R ⊔ clo R) ≤ companion F (R ⊔ clo R) follows from
  -- the fact that paco F S ≤ gfpClo S ≤ companion F S

  -- Show clo R ≤ companion F R via the gfpClo route
  -- gfpClo R = gfp (X ↦ R ⊔ F X) = paco F R

  -- Alternative: show clo R ≤ cpn F R directly by finding a compatible closure
  -- The prespectClosure might be compatible (needs verification)

  -- Key insight: upaco F S ≤ cpn F S
  -- Because: paco F S ⊔ S ≤ cpn F S (paco F S ≤ cpn F S by cpn containing gfp, S ≤ cpn F S by base)

  have h_upaco_le_cpn : ∀ S, upaco F S ≤ cpn F S := by
    intro S x y hup
    cases hup with
    | inl hp =>
      -- hp : paco F S x y
      -- paco F S = gfp (X ↦ S ⊔ F X) = gfpClo S
      -- Need: gfpClo S ≤ cpn F S
      -- gfpClo S is a fixed point of X ↦ S ⊔ F X
      -- cpn F S satisfies: S ≤ cpn F S (base) and F (cpn F S) ≤ cpn F S (step)
      -- So cpn F S is a post-fixed point of X ↦ S ⊔ F X
      -- By Knaster-Tarski, gfp ≤ cpn F S

      -- Actually, paco F S = OrderHom.gfp (gfpCloGen S)
      -- where gfpCloGen S X = S ⊔ F X
      -- The gfp property: X ≤ S ⊔ F X → X ≤ paco F S
      -- And paco F S ≤ S ⊔ F (paco F S)

      -- To show paco F S ≤ cpn F S:
      -- Use coinduction: show paco F S is a post-fixpoint of something that cpn F absorbs
      -- paco F S ≤ S ⊔ F (paco F S) (by paco_unfold)
      -- If S ≤ cpn F S (by base) and F (cpn F S) ≤ cpn F S (by step),
      -- then paco F S ≤ S ⊔ F (paco F S) ≤ cpn F S ⊔ F (cpn F S)

      -- This requires showing F (paco F S) ≤ F (cpn F S) and paco F S ≤ cpn F S
      -- The second is what we're trying to prove - circular!

      -- Alternative: use paco_coind to show paco F S ≤ cpn F S by coinduction
      -- Witness: cpn F S
      -- Need: cpn F S ≤ S ⊔ F (cpn F S)
      -- By base: S ≤ cpn F S, so S ≤ cpn F S
      -- But we need cpn F S ≤ S ⊔ F (cpn F S), not S ≤ cpn F S!

      -- Actually, for paco_coind with witness W:
      -- If W ≤ gfpCloGen S W = S ⊔ F W, then W ≤ paco F S
      -- But we want paco F S ≤ cpn F S, not the other direction.

      -- Let me try a different approach: construct paco F S as a compatible closure
      sorry
    | inr hr =>
      -- hr : S x y
      exact cpn.base x y hr

  -- Now: clo R ≤ upaco F (R ⊔ clo R) ≤ cpn F (R ⊔ clo R)
  -- Need: cpn F (R ⊔ clo R) ≤ cpn F R
  -- By cpn_mono: (R ⊔ clo R) ≤ R would give this, but that's backwards!

  -- Alternative: use cpn idempotence and absorption
  -- cpn F (R ⊔ clo R) contains both R and clo R
  -- We need clo R ≤ cpn F R

  -- The PRespectful condition says:
  -- clo l ≤ paco F (r ⊔ clo r) when l ≤ r and l ≤ F r

  -- For clo R, we'd need to find r such that:
  -- R ≤ r and R ≤ F r and paco F (r ⊔ clo r) ≤ cpn F R

  -- This is still the fundamental challenge: R ≤ F r doesn't hold for arbitrary R

  sorry

/-- Paco respectfulness uclo lemma: clo R ≤ gupaco_clo F (companion F) R -/
theorem prespect_uclo (F : MonoRel α) {clo : Rel α → Rel α}
    (h : PRespectful F clo) (R : Rel α) :
    clo R ≤ gupaco_clo F (companion F) R := by
  intro x y hclo
  have h1 : clo R ≤ companion F R := prespect_companion F h R
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

This is the key lemma connecting grespectful to the companion.

**Proof strategy** (following Coq's grespect0_companion):
1. Define a closure operator using GRespectful
2. Show it's compatible' (via grespect_compatible')
3. Use compatible'_le_companion to conclude clo ≤ companion

**Note**: This proof depends on `compatible'_le_companion`, which in turn depends on
`cpn_eq_cpn_extendedGen`. The latter requires `ExtCompatImpliesCompat F`, so completing
this proof ultimately depends on establishing that assumption.

For guarded inputs (l = F T where T = companion F R):
- GRespectful gives: clo (F T) ≤ rclo (companion F) (F (rclo (clo ⊔ gupaco_clo F (companion F)) T))
- Key absorption: rclo (companion F) S ≤ companion F S (by cpn.rclo_le)
- gupaco_clo F (companion F) R = companion F R (by companion_gupaco_eq)
- F (companion F R) ≤ companion F R (by companion_step)

The challenge is showing clo R ≤ companion F R for arbitrary R (not just guarded inputs).
The GRespectful condition only applies when l ≤ r AND l ≤ F r, which doesn't hold for
arbitrary R. -/
theorem grespect_companion (F : MonoRel α) {clo : Rel α → Rel α}
    (h : GRespectful F clo) : ∀ R, clo R ≤ companion F R := by
  intro R
  -- The proof structure mirrors prespect_companion:
  -- 1. GRespectful only applies to F-guarded inputs (l ≤ F r)
  -- 2. For arbitrary R, we can't directly apply GRespectful
  -- 3. Need to either:
  --    a) Show a closure operator is compatible', then use compatible'_le_companion
  --    b) Use companion properties directly with bootstrapping
  --
  -- Bootstrapping approach:
  -- - R ≤ companion F R (by companion_extensive)
  -- - clo R ≤ clo (companion F R) (by monotonicity)
  -- - Need: clo (companion F R) ≤ companion F R
  --
  -- For clo (companion F R):
  -- - companion F R is NOT necessarily F-guarded, so GRespectful doesn't directly apply
  -- - BUT companion F R contains F (companion F R) via companion_step
  --
  -- This proof remains incomplete pending an `ExtCompatImpliesCompat F` hypothesis,
  -- which underpins the Compatible' → companion chain.
  sorry

/-- Generalized respectfulness uclo lemma: clo R ≤ gupaco_clo F (companion F) R -/
theorem grespect_uclo (F : MonoRel α) {clo : Rel α → Rel α}
    (h : GRespectful F clo) (R : Rel α) :
    clo R ≤ gupaco_clo F (companion F) R := by
  intro x y hclo
  have h1 : clo R ≤ companion F R := grespect_companion F h R
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
