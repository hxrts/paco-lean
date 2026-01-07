import Paco.UpTo.Cpn

/-!
# GPaco with Closure (gpaco_clo)

The full gpaco definition following Coq:
  gpaco_clo clo r rg = rclo clo (paco (F ∘ rclo clo) (rg ⊔ r) ⊔ r)

## Main Definitions

- `composeRclo F clo`: Composed generating function F ∘ rclo clo
- `gpaco_clo F clo r rg`: Generalized paco with user-defined closure
- `gupaco_clo F clo r`: Symmetric version (guard = accumulator)
- `WCompatible F clo`: Weak compatibility

## Key Theorems

- `gpaco_clo_coind`: Full coinduction principle (Coq's gpacoN_cofix)
- `gpaco_clo_gupaco`: Gupaco absorption into gpaco
- `gpaco_clo_final`: GPaco is contained in gfp when clo is compatible

## References

- [Paco paper (POPL 2013)](https://plv.mpi-sws.org/paco/)
- [GPaco paper (CPP 2020)](https://paulhe.com/assets/gpaco.pdf)
- [Paco Coq: gpacoN.v](https://github.com/snu-sf/paco)
-/

namespace Paco

variable {α : Type*}

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
          -- Use induction on rclo structure to handle l elements that become gpaco_clo
          intro x' y' huprclo
          induction huprclo with
          | @base x' y' hbase =>
            simp only [upaco, Rel.union_apply] at hbase
            cases hbase with
            | inl hp => exact rclo.base (Or.inl hp)
            | inr hrglr =>
              cases hrglr with
              | inl hrgl =>
                cases hrgl with
                | inl hrg => exact rclo.base (Or.inr (Or.inl hrg))
                | inr hl' =>
                  -- l element: use IN to get gpaco_clo, then use rclo.mono
                  have hIN := IN x' y' hl'
                  simp only [gpaco_clo_def] at hIN
                  -- hIN : rclo clo (paco P ((rg ⊔ l) ⊔ r) ⊔ r) x' y'
                  have h_r_le : paco (composeRclo F clo) ((rg ⊔ l) ⊔ r) ⊔ r ≤
                                paco (composeRclo F clo) ((rg ⊔ l) ⊔ r) ⊔ (rg ⊔ r) :=
                    sup_le_sup_left le_sup_right _
                  exact rclo.mono h_r_le x' y' hIN
              | inr hr' => exact rclo.base (Or.inr (Or.inr hr'))
          | @clo x' y' R' hR' hcloR' ih =>
            exact rclo.clo R' ih hcloR'
        apply F.mono' h_rclo_le u v h_unfold
      · exact hpaco_ab
    · intro a b hr_ab
      exact rclo.base (Or.inr hr_ab)
  -- h_inner : paco ... ⊔ r ≤ rclo clo (paco ... ⊔ r)
  -- hgpaco : rclo clo (paco P ((rg ⊔ l) ⊔ r) ⊔ r) x y
  -- Goal: rclo clo (paco P (rg ⊔ r) ⊔ r) x y
  -- Use: rclo.mono h_inner gives rclo clo (paco ⊔ r) ≤ rclo clo (rclo clo (paco ⊔ r))
  -- Then rclo.rclo_rclo collapses the nested rclo
  exact rclo.rclo_rclo x y (rclo.mono h_inner x y hgpaco)

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

Proof strategy: Direct induction on the source rclo structure.
1. For base case (paco P G): use paco_mon since G ≤ rr ⊔ r
2. For base case (G itself): use rclo.mono since G = gpaco r rg ≤ gpaco r rr (by rg ≤ rr)
3. For clo case: gpaco r rr = rclo clo (...) is closed under clo via clo_rclo -/
theorem gpaco_clo_gupaco (F : MonoRel α) (clo : Rel α → Rel α)
    (_h_mono : CloMono clo) (_h_compat : Compatible F clo)
    (r rg : Rel α) :
    gupaco_clo F clo (gpaco_clo F clo r rg) ≤ gpaco_clo F clo r rg := by
  let G := gpaco_clo F clo r rg
  let P := composeRclo F clo
  -- gupaco G = rclo clo (paco P (G ⊔ G) ⊔ G) = rclo clo (paco P G ⊔ G)
  -- gpaco r rg = rclo clo (paco P (rg ⊔ r) ⊔ r)
  -- Use gpaco_clo_coind to prove gupaco G ≤ gpaco r rg
  apply gpaco_clo_coind F clo r rg (gupaco_clo F clo G)
  intro rr INC CIH
  -- INC : rg ≤ rr
  -- CIH : gupaco G ≤ rr (i.e., rclo clo (paco P G ⊔ G) ≤ rr)
  -- Goal: gupaco G ≤ gpaco r rr (i.e., rclo clo (paco P G ⊔ G) ≤ rclo clo (paco P (rr ⊔ r) ⊔ r))
  -- Direct induction on source rclo structure
  simp only [gupaco_clo_def, gpaco_clo_def, sup_idem]
  intro x y hgup
  induction hgup with
  | @base x y hbase =>
    cases hbase with
    | inl hpaco =>
      -- hpaco : paco P G x y
      -- From CIH: paco P G ≤ gupaco G ≤ rr, so G ≤ rr (since G ≤ gupaco G)
      have h_G_le_rr : G ≤ rr := by
        intro a b hG
        have h1 : gupaco_clo F clo G a b := by
          simp only [gupaco_clo_def, gpaco_clo_def, sup_idem]
          exact rclo.base (Or.inr hG)
        exact CIH a b h1
      -- G ≤ rr implies G ≤ rr ⊔ r, so paco P G ≤ paco P (rr ⊔ r)
      have hG_le_rr_r : G ≤ rr ⊔ r := Rel.le_trans h_G_le_rr le_sup_left
      have hpaco' := paco_mon P hG_le_rr_r x y hpaco
      exact rclo.base (Or.inl hpaco')
    | inr hG =>
      -- hG : G x y = gpaco_clo F clo r rg x y
      -- Goal: rclo clo (paco P (rr ⊔ r) ⊔ r) x y
      -- G = rclo clo (paco P (rg ⊔ r) ⊔ r)
      -- Since rg ≤ rr (INC), we have rg ⊔ r ≤ rr ⊔ r
      -- So paco P (rg ⊔ r) ≤ paco P (rr ⊔ r) by paco_mon
      -- Thus paco P (rg ⊔ r) ⊔ r ≤ paco P (rr ⊔ r) ⊔ r
      -- And rclo clo (paco P (rg ⊔ r) ⊔ r) ≤ rclo clo (paco P (rr ⊔ r) ⊔ r) by rclo.mono
      have h_rg_r_le : rg ⊔ r ≤ rr ⊔ r := sup_le_sup_right INC r
      have h_paco_le : paco P (rg ⊔ r) ⊔ r ≤ paco P (rr ⊔ r) ⊔ r :=
        sup_le_sup_right (paco_mon P h_rg_r_le) r
      exact rclo.mono h_paco_le x y hG
  | @clo x y R' hR' hcloR' ih =>
    -- hcloR' : clo R' x y where R' ≤ rclo clo (paco P (rr ⊔ r) ⊔ r) (by ih)
    -- Goal: rclo clo (paco P (rr ⊔ r) ⊔ r) x y
    -- rclo clo X is closed under clo (by clo_rclo)
    exact rclo.clo R' ih hcloR'

/-- Key accumulation lemma: gupaco (gpaco r rg) ≤ gpaco r rg.

This is the crucial property that allows building up gpaco proofs incrementally.
When you have a gpaco predicate and use it as the accumulator for gupaco,
the result is still contained in the original gpaco.

Note: This requires `clo` to be compatible and monotone. See `gpaco_clo_gupaco` for the proof. -/
theorem gpaco_gupaco (F : MonoRel α) (clo : Rel α → Rel α)
    (h_mono : CloMono clo) (h_compat : Compatible F clo)
    (r rg : Rel α) :
    gupaco_clo F clo (gpaco_clo F clo r rg) ≤ gpaco_clo F clo r rg :=
  gpaco_clo_gupaco F clo h_mono h_compat r rg

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

This is the key theorem connecting weak compatibility to strong compatibility.
The proof uses coinduction to show F R ≤ paco P R, which embeds into gupaco R. -/
theorem wcompat_compat_gupaco (F : MonoRel α) {clo : Rel α → Rel α}
    (h_mono : CloMono clo) (h_wcompat : WCompatible F clo)
    (h_idemp : ∀ R, gupaco_clo F clo (gupaco_clo F clo R) ≤ gupaco_clo F clo R) :
    Compatible F (gupaco_clo F clo) := by
  intro R
  -- Goal: gupaco_clo F clo (F R) ≤ F (gupaco_clo F clo R)
  -- Note: gupaco_clo F clo X = gpaco_clo F clo X X = rclo clo (paco P (X ⊔ X) ⊔ X)
  -- where P = composeRclo F clo
  let P := composeRclo F clo
  -- Key lemma: F R ≤ paco P (R ⊔ R) using coinduction
  have h_FR_le_paco : F R ≤ paco P (R ⊔ R) := by
    -- Use paco_coind' with witness = F R
    apply paco_coind' P (R ⊔ R) (F R)
    intro x y hFR
    -- Goal: P (F R ⊔ (R ⊔ R)) x y = F (rclo clo (F R ⊔ (R ⊔ R))) x y
    -- Since R ≤ F R ⊔ (R ⊔ R) ≤ rclo clo (...), by F mono we get result
    have h_R_le : R ≤ rclo clo (F R ⊔ (R ⊔ R)) := fun a b hr =>
      rclo.base (Or.inr (Or.inl hr))
    exact F.mono' h_R_le x y hFR
  -- F R ≤ paco P (R ⊔ R) ≤ rclo clo (paco P (R ⊔ R) ⊔ R) = gupaco R
  have h_FR_le_gupaco : F R ≤ gupaco_clo F clo R := fun x y hFR =>
    rclo.base (Or.inl (h_FR_le_paco x y hFR))
  -- paco P (F R ⊔ F R) ≤ paco P (gupaco R ⊔ gupaco R) ≤ gupaco (gupaco R) ≤ gupaco R
  have h_paco_FR_le : paco P (F R ⊔ F R) ≤ gupaco_clo F clo R := fun x y hpaco =>
    let hpaco' := paco_mon P (sup_le_sup h_FR_le_gupaco h_FR_le_gupaco) x y hpaco
    h_idemp R x y (rclo.base (Or.inl hpaco'))
  -- Now prove the main result by induction on rclo
  -- gupaco F clo (F R) = rclo clo (paco P (F R ⊔ F R) ⊔ F R)
  intro x y hgup
  induction hgup with
  | @base x y hbase =>
    cases hbase with
    | inl hpaco =>
      -- hpaco : paco P (F R ⊔ F R) x y
      -- Goal: F (gupaco_clo F clo R) x y
      have hunf := paco_unfold P (F R ⊔ F R) x y hpaco
      -- hunf : P (upaco P (F R ⊔ F R)) x y = F (rclo clo (paco P (F R ⊔ F R) ⊔ (F R ⊔ F R))) x y
      -- Show: rclo clo (paco P (F R ⊔ F R) ⊔ (F R ⊔ F R)) ≤ gupaco R
      have h_inner_le : paco P (F R ⊔ F R) ⊔ (F R ⊔ F R) ≤ gupaco_clo F clo R :=
        sup_le h_paco_FR_le (sup_le h_FR_le_gupaco h_FR_le_gupaco)
      have h_rclo_le : rclo clo (paco P (F R ⊔ F R) ⊔ (F R ⊔ F R)) ≤ gupaco_clo F clo R :=
        fun a b hrclo => rclo.rclo_rclo a b (rclo.mono h_inner_le a b hrclo)
      exact F.mono' h_rclo_le x y hunf
    | inr hFR =>
      -- hFR : F R x y
      -- Goal: F (gupaco_clo F clo R) x y
      exact F.mono' (r_le_gpaco_clo F clo R R) x y hFR
  | @clo x y R' hR' hcloR' ih =>
    -- hcloR' : clo R' x y with R' ≤ F (gupaco_clo F clo R)
    -- ih : R' ≤ F (gupaco_clo F clo R)
    have h1 : clo R' ≤ clo (F (gupaco_clo F clo R)) := h_mono R' _ ih
    have h2 := h_wcompat (gupaco_clo F clo R) x y (h1 x y hcloR')
    -- h2 : F (gupaco_clo F clo (gupaco_clo F clo R)) x y
    exact F.mono' (h_idemp R) x y h2

/-- cpn F X ≤ rclo (cpn F) X (cpn embeds into rclo via rclo.clo) -/
theorem cpn.le_rclo (F : MonoRel α) (X : Rel α) : cpn F X ≤ rclo (cpn F) X := by
  intro x y ⟨clo, h_mono, h_compat, hclo⟩
  have h1 : clo X ≤ cpn F X := cpn.greatest h_mono h_compat
  apply rclo.clo X
  · exact rclo.base_le
  · exact h1 x y hclo

/-- gupaco_clo F (cpn F) is compatible with F.

Proof uses wcompat_compat_gupaco with cpn's weak compatibility and idempotence. -/
theorem cpn.gupaco_compat (F : MonoRel α) : Compatible F (gupaco_clo F (cpn F)) := by
  apply wcompat_compat_gupaco F cpn.cpn_cloMono (cpn.wcompat F)
  -- Idempotence: gupaco (gupaco R) ≤ gupaco R
  intro R
  simpa [gupaco_clo_def] using
    (gpaco_gupaco F (cpn F) cpn.cpn_cloMono cpn.compat R R)

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
    -- First: cpn F R ≤ rclo (cpn F) R via rclo.clo_base
    have h1 : rclo (cpn F) R x y := rclo.clo_base x y hcpn
    -- Then: rclo (cpn F) R ≤ rclo (cpn F) (paco ... ⊔ R) via rclo.mono
    have h2 : R ≤ paco (composeRclo F (cpn F)) R ⊔ R := le_sup_right
    exact rclo.mono h2 x y h1

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
  -- To show gupaco_clo F clo S ≤ gupaco_clo F (cpn F) S, we need to handle both:
  -- 1. The change from rclo clo to rclo (cpn F)
  -- 2. The change from paco (composeRclo F clo) to paco (composeRclo F (cpn F))
  have h_rclo_clo_le : ∀ R, rclo clo R ≤ rclo (cpn F) R := fun R => rclo.mono_clo h_clo_le
  have h_paco_le : paco (composeRclo F clo) S ≤ paco (composeRclo F (cpn F)) S := by
    apply paco_mon_gen
    · intro R x y hFrclo
      simp only [composeRclo_def] at hFrclo ⊢
      exact F.mono' (h_rclo_clo_le R) x y hFrclo
    · exact Rel.le_refl S
  have h2 : gupaco_clo F clo S ≤ gupaco_clo F (cpn F) S := by
    simp only [gupaco_clo_def, gpaco_clo_def, sup_idem]
    intro x y hrclo
    -- hrclo : rclo clo (paco (composeRclo F clo) S ⊔ S) x y
    -- Goal: rclo (cpn F) (paco (composeRclo F (cpn F)) S ⊔ S) x y
    have h_inner_le : paco (composeRclo F clo) S ⊔ S ≤ paco (composeRclo F (cpn F)) S ⊔ S :=
      sup_le_sup_right h_paco_le S
    have h_rclo_inner : rclo clo (paco (composeRclo F clo) S ⊔ S) ≤
                        rclo clo (paco (composeRclo F (cpn F)) S ⊔ S) := rclo.mono h_inner_le
    have h_rclo_outer : rclo clo (paco (composeRclo F (cpn F)) S ⊔ S) ≤
                        rclo (cpn F) (paco (composeRclo F (cpn F)) S ⊔ S) := h_rclo_clo_le _
    exact h_rclo_outer x y (h_rclo_inner x y hrclo)
  have h3 : gupaco_clo F (cpn F) S = cpn F S := cpn.gupaco_eq F S
  calc cpn F (upaco (composeRclo F clo) S)
      ≤ cpn F (gupaco_clo F clo S) := cpn.mono h1
    _ ≤ cpn F (gupaco_clo F (cpn F) S) := cpn.mono h2
    _ = cpn F (cpn F S) := by rw [h3]
    _ ≤ cpn F S := cpn.cpn_cpn

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

end Paco
