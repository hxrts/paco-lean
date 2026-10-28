import Paco.UpTo.Cpn

/-!
# GPaco with Closure (gpacoClo)

The full gpaco definition following Coq:
  gpacoClo clo r rg = rclo clo (paco (F ∘ rclo clo) (rg ⊔ r) ⊔ r)

## Main Definitions

- `composeRclo F clo`: Composed generating function F ∘ rclo clo
- `gpacoClo F clo r rg`: Generalized paco with user-defined closure
- `gupacoClo F clo r`: Symmetric version (guard = accumulator)
- `WCompatible F clo`: Weak compatibility

## Key Theorems

- `gpacoClo_coind`: Full coinduction principle (Coq's gpacoN_cofix)
- `gpacoClo_gupaco`: Gupaco absorption into gpaco
- `gpacoClo_final`: GPaco is contained in gfp when clo is compatible

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
## GPaco with Closure (gpacoClo)
-/

/-- Generalized paco with user-defined closure operator.

`gpacoClo F clo r rg` is the main predicate for up-to coinduction:
- `clo`: User closure operator (e.g., congruence, transitivity)
- `r`: Accumulator (immediately available facts)
- `rg`: Guard (facts available after progress)

Definition: rclo clo (paco (F ∘ rclo clo) (rg ⊔ r) ⊔ r) -/
def gpacoClo (F : MonoRel α) (clo : Rel α → Rel α) (r rg : Rel α) : Rel α :=
  rclo clo (paco (composeRclo F clo) (rg ⊔ r) ⊔ r)

/-- Symmetric version: guard equals accumulator -/
def gupacoClo (F : MonoRel α) (clo : Rel α → Rel α) (r : Rel α) : Rel α :=
  gpacoClo F clo r r

/-!
## gpacoClo Basic Properties
-/

theorem gpacoClo_def (F : MonoRel α) (clo : Rel α → Rel α) (r rg : Rel α) :
    gpacoClo F clo r rg = rclo clo (paco (composeRclo F clo) (rg ⊔ r) ⊔ r) := rfl

theorem gupacoClo_def (F : MonoRel α) (clo : Rel α → Rel α) (r : Rel α) :
    gupacoClo F clo r = gpacoClo F clo r r := rfl

/-- r injects into gpacoClo -/
theorem r_le_gpacoClo (F : MonoRel α) (clo : Rel α → Rel α) (r rg : Rel α) :
    r ≤ gpacoClo F clo r rg := by
  intro x y hr
  exact rclo.base (Or.inr hr)

/-- paco (F ∘ rclo clo) (rg ⊔ r) injects into gpacoClo -/
theorem paco_le_gpacoClo (F : MonoRel α) (clo : Rel α → Rel α) (r rg : Rel α) :
    paco (composeRclo F clo) (rg ⊔ r) ≤ gpacoClo F clo r rg := by
  intro x y hp
  exact rclo.base (Or.inl hp)

/-- gpacoClo is monotone in r -/
theorem gpacoClo_mon_r (F : MonoRel α) (clo : Rel α → Rel α) (rg : Rel α)
    {r r' : Rel α} (hr : r ≤ r') : gpacoClo F clo r rg ≤ gpacoClo F clo r' rg := by
  unfold gpacoClo
  apply rclo.mono
  apply sup_le_sup
  · exact paco_mon (composeRclo F clo) (sup_le_sup_left hr rg)
  · exact hr

/-- gpacoClo is monotone in rg -/
theorem gpacoClo_mon_rg (F : MonoRel α) (clo : Rel α → Rel α) (r : Rel α)
    {rg rg' : Rel α} (hrg : rg ≤ rg') : gpacoClo F clo r rg ≤ gpacoClo F clo r rg' := by
  unfold gpacoClo
  apply rclo.mono
  apply sup_le_sup_right
  exact paco_mon (composeRclo F clo) (sup_le_sup_right hrg r)

/-- gpacoClo is monotone in both r and rg -/
theorem gpacoClo_mon (F : MonoRel α) (clo : Rel α → Rel α)
    {r r' rg rg' : Rel α} (hr : r ≤ r') (hrg : rg ≤ rg') :
    gpacoClo F clo r rg ≤ gpacoClo F clo r' rg' :=
  Rel.le_trans (gpacoClo_mon_r F clo rg hr) (gpacoClo_mon_rg F clo r' hrg)

/-!
## gpacoClo Coinduction Principle

The main coinduction principle: to prove gpacoClo F clo r rg x y,
provide a relation R with R x y such that for any rr extending rg ⊔ R,
we have R ⊆ gpacoClo F clo r rr.
-/

/-- Helper: rclo preserves containment in gpacoClo -/
theorem rclo_gpacoClo_le (F : MonoRel α) (clo : Rel α → Rel α) (r rg rg' : Rel α)
    (hrg : rg ≤ rg') :
    rclo clo (paco (composeRclo F clo) (rg ⊔ r) ⊔ r) ≤ gpacoClo F clo r rg' := by
  unfold gpacoClo
  apply rclo.mono
  apply sup_le_sup_right
  exact paco_mon (composeRclo F clo) (sup_le_sup_right hrg r)

/-- Full coinduction principle for gpacoClo (Coq's gpacoN_cofix).

To prove `l ≤ gpacoClo F clo r rg`, show that for any `rr` with
`rg ≤ rr` (INC) and `l ≤ rr` (CIH), we have `l ≤ gpacoClo F clo r rr`.

The key insight (from Coq): First get `IN: l ≤ gpaco r (rg ⊔ l)` by instantiating
OBG with rr = rg ⊔ l. Then use coinduction to collapse `paco P ((rg ⊔ l) ⊔ r)`
back to `paco P (rg ⊔ r)`. The `l` elements get transformed via IN into the
gpaco structure, which lands in `rclo clo (W ⊔ S)` for the coinductive witness. -/
theorem gpacoClo_coind (F : MonoRel α) (clo : Rel α → Rel α) (r rg : Rel α)
    (l : Rel α)
    (OBG : ∀ rr, rg ≤ rr → l ≤ rr → l ≤ gpacoClo F clo r rr) :
    l ≤ gpacoClo F clo r rg := by
  have IN : l ≤ gpacoClo F clo r (rg ⊔ l) := OBG (rg ⊔ l) le_sup_left le_sup_right
  intro x y hlxy
  have hgpaco := IN x y hlxy
  simp only [gpacoClo_def] at hgpaco ⊢
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
          -- Use induction on rclo structure to handle l elements that become gpacoClo
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
                  -- l element: use IN to get gpacoClo, then use rclo.mono
                  have hIN := IN x' y' hl'
                  simp only [gpacoClo_def] at hIN
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

/-- Pointwise coinduction for gpacoClo.

This is the pointwise version of `gpacoClo_coind`, analogous to `paco_coind`.
It avoids needing to apply the resulting relation to `x y` manually. -/
theorem gpacoClo_coind' (F : MonoRel α) (clo : Rel α → Rel α) (r rg : Rel α)
    (l : Rel α) {x y : α}
    (OBG : ∀ rr, rg ≤ rr → l ≤ rr → l ≤ gpacoClo F clo r rr)
    (hxy : l x y) : gpacoClo F clo r rg x y :=
  (gpacoClo_coind F clo r rg l OBG) x y hxy

/-- Simple coinduction for gpacoClo: prove via paco with F-progress.

To prove `gpacoClo F clo r rg x y`, find R with R x y such that
R ⊆ F (rclo clo (R ⊔ upaco (F ∘ rclo clo) (rg ⊔ r))) ⊔ r.

Note: When R a b gives r a b (base case), no F-progress is needed. -/
theorem gpacoClo_cofix (F : MonoRel α) (clo : Rel α → Rel α) (r rg : Rel α)
    (R : Rel α) {x y : α}
    (hR : R ≤ F (rclo clo (R ⊔ upaco (composeRclo F clo) (rg ⊔ r))) ⊔ r)
    (hxy : R x y) : gpacoClo F clo r rg x y := by
  unfold gpacoClo
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

When clo = id, gpacoClo reduces to something equivalent to gpaco.
-/

/-- With identity closure, composeRclo simplifies to F -/
theorem composeRclo_id (F : MonoRel α) : composeRclo F id = F := by
  cases F with
  | mk f hf =>
    simp only [composeRclo]
    congr 1
    funext R
    simp only [Function.comp_apply, rclo.rclo_id]

/-- With identity closure, gpacoClo simplifies to gpaco -/
theorem gpacoClo_id (F : MonoRel α) (r rg : Rel α) :
    gpacoClo F id r rg = paco F (rg ⊔ r) ⊔ r := by
  simp only [gpacoClo_def, rclo.rclo_id, composeRclo_id]

/-!
## Accumulation in gpacoClo
-/

/-- gupacoClo absorbs into gpacoClo (requires compatible monotone closure).

This is a key accumulation lemma: facts proven via gupacoClo can be accumulated
back into gpacoClo, enabling compositional proofs.

Proof strategy: Direct induction on the source rclo structure.
1. For base case (paco P G): use paco_mon since G ≤ rr ⊔ r
2. For base case (G itself): use rclo.mono since G = gpaco r rg ≤ gpaco r rr (by rg ≤ rr)
3. For clo case: gpaco r rr = rclo clo (...) is closed under clo via clo_rclo -/
theorem gpacoClo_gupaco (F : MonoRel α) (clo : Rel α → Rel α)
    (_h_mono : CloMono clo) (_h_compat : Compatible F clo)
    (r rg : Rel α) :
    gupacoClo F clo (gpacoClo F clo r rg) ≤ gpacoClo F clo r rg := by
  have _ := _h_mono
  have _ := _h_compat
  let G := gpacoClo F clo r rg
  let P := composeRclo F clo
  -- gupaco G = rclo clo (paco P (G ⊔ G) ⊔ G) = rclo clo (paco P G ⊔ G)
  -- gpaco r rg = rclo clo (paco P (rg ⊔ r) ⊔ r)
  -- Use gpacoClo_coind to prove gupaco G ≤ gpaco r rg
  apply gpacoClo_coind F clo r rg (gupacoClo F clo G)
  intro rr INC CIH
  -- INC : rg ≤ rr
  -- CIH : gupaco G ≤ rr (i.e., rclo clo (paco P G ⊔ G) ≤ rr)
  -- Goal: gupaco G ≤ gpaco r rr (i.e., rclo clo (paco P G ⊔ G) ≤ rclo clo (paco P (rr ⊔ r) ⊔ r))
  -- Direct induction on source rclo structure
  simp only [gupacoClo_def, gpacoClo_def, sup_idem]
  intro x y hgup
  induction hgup with
  | @base x y hbase =>
    cases hbase with
    | inl hpaco =>
      -- hpaco : paco P G x y
      -- From CIH: paco P G ≤ gupaco G ≤ rr, so G ≤ rr (since G ≤ gupaco G)
      have h_G_le_rr : G ≤ rr := by
        intro a b hG
        have h1 : gupacoClo F clo G a b := by
          simp only [gupacoClo_def, gpacoClo_def, sup_idem]
          exact rclo.base (Or.inr hG)
        exact CIH a b h1
      -- G ≤ rr implies G ≤ rr ⊔ r, so paco P G ≤ paco P (rr ⊔ r)
      have hG_le_rr_r : G ≤ rr ⊔ r := Rel.le_trans h_G_le_rr le_sup_left
      have hpaco' := paco_mon P hG_le_rr_r x y hpaco
      exact rclo.base (Or.inl hpaco')
    | inr hG =>
      -- hG : G x y = gpacoClo F clo r rg x y
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

Note: This requires `clo` to be compatible and monotone. See `gpacoClo_gupaco` for the proof. -/
theorem gpaco_gupaco (F : MonoRel α) (clo : Rel α → Rel α)
    (h_mono : CloMono clo) (h_compat : Compatible F clo)
    (r rg : Rel α) :
    gupacoClo F clo (gpacoClo F clo r rg) ≤ gpacoClo F clo r rg :=
  gpacoClo_gupaco F clo h_mono h_compat r rg

end Paco
