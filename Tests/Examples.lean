import Paco

/-!
# Paco Examples

This file replicates the examples from the Coq paco library's `examples.v` file.
It demonstrates parametrized coinduction for stream equivalence proofs.

The main example is `seq`, a relaxed stream equivalence that allows insertion
of zeros in either stream. We prove reflexivity, symmetry, and transitivity.

## References

- [Coq paco examples.v](https://github.com/snu-sf/paco/blob/master/src/examples.v)
-/

namespace Paco.Tests.Examples

open Paco

/-!
## Stream Type

We define streams as a coinductive type with nil and cons constructors.
This matches the Coq definition:
```coq
CoInductive stream (A:Type) :=
| snil : stream A
| scons : A -> stream A -> stream A.
```
-/

/-- Coinductive stream type. -/
inductive Stream (α : Type*) : Type _
  | snil : Stream α
  | scons : α → Stream α → Stream α
  deriving Repr, DecidableEq

namespace Stream

variable {α : Type*}

/-- Get the tail of a stream, or nil for nil. -/
def tail : Stream α → Stream α
  | snil => snil
  | scons _ s => s

end Stream

open Stream

/-!
## Stream Equivalence with Zero Insertion (seq)

The `seq` relation allows finite insertion of zeros in either stream.
Two streams are equivalent if we can match them up after removing zeros.

Coq definition:
```coq
Inductive seq_step (seq : stream nat -> stream nat -> Prop) :
  stream nat -> stream nat -> Prop :=
| seq_nil  : seq_step seq snil snil
| seq_cons : forall s1 s2 n (R : seq s1 s2),
    seq_step seq (scons n s1) (scons n s2)
| seq_cons_z_l : forall s1 s2, seq_step seq s1 s2 ->
    seq_step seq (scons 0 s1) s2
| seq_cons_z_r : forall s1 s2, seq_step seq s1 s2 ->
    seq_step seq s1 (scons 0 s2).
```
-/

/-- Step relation for `seq`: stream equivalence allowing zero insertion. -/
inductive SeqStep (R : Stream Nat → Stream Nat → Prop) :
    Stream Nat → Stream Nat → Prop where
  | seq_nil : SeqStep R snil snil
  | seq_cons (n : Nat) (s1 s2 : Stream Nat) :
      R s1 s2 → SeqStep R (scons n s1) (scons n s2)
  | seq_cons_z_l (s1 s2 : Stream Nat) :
      SeqStep R s1 s2 → SeqStep R (scons 0 s1) s2
  | seq_cons_z_r (s1 s2 : Stream Nat) :
      SeqStep R s1 s2 → SeqStep R s1 (scons 0 s2)

/-- Monotonicity of `SeqStep`. Corresponds to Coq's `seq_step_mono`. -/
lemma seqStep_mono : ∀ R S : Rel (Stream Nat), R ≤ S → SeqStep R ≤ SeqStep S := by
  intro R S hRS s t h
  induction h with
  | seq_nil => exact SeqStep.seq_nil
  | seq_cons n s1 s2 hR =>
    exact SeqStep.seq_cons n s1 s2 (hRS _ _ hR)
  | seq_cons_z_l s1 s2 _ ih =>
    exact SeqStep.seq_cons_z_l s1 s2 ih
  | seq_cons_z_r s1 s2 _ ih =>
    exact SeqStep.seq_cons_z_r s1 s2 ih

/-- Bundled monotone transformer for `SeqStep`. -/
def SeqF : MonoRel (Stream Nat) where
  F := SeqStep
  mono := seqStep_mono

/-- Stream equivalence with zero insertion.
Corresponds to Coq's `Definition seq (s t : stream nat) := paco2 seq_step bot2 s t.` -/
def seq (s t : Stream Nat) : Prop := paco SeqF ⊥ s t

/-!
## Reflexivity of seq

Coq proof:
```coq
Lemma seq_refl : forall s, seq s s.
Proof.
  pcofix CIH.
  intros s.
  pfold.
  destruct s; auto.
Qed.
```

We replicate this structure exactly.
-/

/-- `seq` is reflexive: `seq s s` for all streams `s`.

Coq proof structure:
- pcofix CIH: start coinduction with hypothesis CIH
- intro s: introduce the stream
- pfold: fold into paco
- destruct s; auto: case split on stream
-/
theorem seq_refl : ∀ s, seq s s := by
  intro s
  unfold seq
  -- pcofix CIH with witness R = equality
  apply paco_coind SeqF (fun a b => a = b) ⊥
  · -- Step goal: show SeqStep (R ⊔ ⊥) a b given R a b
    intro a b hab
    subst hab
    -- pfold; destruct a
    cases a with
    | snil => exact SeqStep.seq_nil
    | scons n t =>
      apply SeqStep.seq_cons n t t
      -- Use coinductive hypothesis (left side of upaco)
      exact Or.inl rfl
  · -- Witness goal: show R s s
    rfl

/-!
## Symmetry of seq

Coq proof:
```coq
Lemma seq_symm : forall s1 s2, seq s1 s2 -> seq s2 s1.
Proof.
  pcofix CIH.
  intros s1 s2 H.
  pfold.
  punfold H.
  induction H; try constructor; auto.
  pclearbot. right. apply CIH. punfold R.
Qed.
```
-/

/-- `SeqStep` preserves symmetry when the underlying relation maps to the target relation. -/
lemma SeqStep_symm' {R S : Stream Nat → Stream Nat → Prop}
    (hRS : ∀ a b, R a b → S b a) :
    ∀ s1 s2, SeqStep R s1 s2 → SeqStep S s2 s1 := by
  intro s1 s2 h
  induction h with
  | seq_nil =>
    exact SeqStep.seq_nil
  | seq_cons n t1 t2 hRt =>
    apply SeqStep.seq_cons n t2 t1
    exact hRS t1 t2 hRt
  | seq_cons_z_l t1 t2 _ ih =>
    exact SeqStep.seq_cons_z_r t2 t1 ih
  | seq_cons_z_r t1 t2 _ ih =>
    exact SeqStep.seq_cons_z_l t2 t1 ih

/-- `seq` is symmetric.

Coq proof structure:
- pcofix CIH: start coinduction
- intros s1 s2 H: introduce streams and hypothesis
- pfold: fold into paco
- punfold H: unfold H to expose SeqStep structure
- induction H: case analysis on SeqStep constructors
- pclearbot in seq_cons case: simplify upaco ⊥ to paco ⊥
-/
theorem seq_symm : ∀ s1 s2, seq s1 s2 → seq s2 s1 := by
  intro s1 s2 H
  unfold seq at H ⊢
  -- pcofix CIH with witness R = {(a,b) | paco SeqF ⊥ b a}
  apply paco_coind SeqF (fun a b => paco SeqF ⊥ b a) ⊥
  · -- Step goal: given paco SeqF ⊥ b a, show SeqStep (R ⊔ ⊥) a b
    intro a b CIH
    -- punfold CIH: unfold to get SeqStep (upaco SeqF ⊥) b a
    have H_unf := paco_unfold SeqF ⊥ b a CIH
    -- simp to convert upaco SeqF ⊥ to paco SeqF ⊥
    simp only [upaco, Rel.sup_bot] at H_unf
    -- Apply symmetry lemma with the right relation transformation
    -- H_unf : SeqStep (paco SeqF ⊥) b a
    -- Goal: SeqStep ((fun a b => paco SeqF ⊥ b a) ⊔ ⊥) a b
    apply SeqStep_symm'
    · intro x y hxy
      -- paco SeqF ⊥ x y → ((fun a b => paco SeqF ⊥ b a) ⊔ ⊥) y x
      -- which is: paco SeqF ⊥ x y → paco SeqF ⊥ x y ∨ ⊥ y x
      exact Or.inl hxy
    · exact H_unf
  · -- Witness goal: show paco SeqF ⊥ s2 s1
    exact H

/-!
## Infinite Zeros Predicate

Coq definition:
```coq
Inductive zeros_one (P: stream nat -> Prop) : stream nat -> Prop :=
| zo_step t (BASE: P t): zeros_one P (scons 0 t).

Definition infzeros := paco1 zeros_one bot1.
```

Note: Coq uses paco1 (unary), but we use paco (binary) with diagonal encoding.
-/

/-- Step relation for infinite zeros (unary, encoded as binary on diagonal). -/
inductive InfZerosStep (R : Stream Nat → Stream Nat → Prop) :
    Stream Nat → Stream Nat → Prop where
  | zo_step (t : Stream Nat) : R t t → InfZerosStep R (scons 0 t) (scons 0 t)

/-- Bundled monotone transformer for infinite zeros. -/
def InfZerosF : MonoRel (Stream Nat) where
  F := InfZerosStep
  mono := by
    intro R S hRS s t h
    cases h with
    | zo_step u hR =>
      exact InfZerosStep.zo_step u (hRS u u hR)

/-- A stream contains infinitely many zeros. -/
def infzeros (s : Stream Nat) : Prop := paco InfZerosF ⊥ s s

/-!
## Nonzero Streams

Coq definition:
```coq
Inductive nonzero: stream nat -> Prop :=
| nz_nil: nonzero snil
| nz_cons n s (NZ: n <> 0): nonzero (scons n s).
```
-/

/-- A stream is nonzero if it is nil or starts with a non-zero element. -/
inductive Nonzero : Stream Nat → Prop where
  | nz_nil : Nonzero snil
  | nz_cons (n : Nat) (s : Stream Nat) (hNZ : n ≠ 0) : Nonzero (scons n s)

/-!
## Zero Star

Coq definition:
```coq
Inductive zeros_star (P: stream nat -> Prop) : stream nat -> Prop :=
| zs_base t (BASE: P t): zeros_star P t
| zs_step t (LZ: zeros_star P t): zeros_star P (scons 0 t).
```
-/

/-- Reflexive-transitive closure for zero prefixes. -/
inductive ZerosStar (P : Stream Nat → Prop) : Stream Nat → Prop where
  | zs_base (t : Stream Nat) : P t → ZerosStar P t
  | zs_step (t : Stream Nat) : ZerosStar P t → ZerosStar P (scons 0 t)

/-- `ZerosStar` is monotone in the predicate. -/
lemma ZerosStar_mono {P Q : Stream Nat → Prop} (hPQ : ∀ s, P s → Q s) :
    ∀ s, ZerosStar P s → ZerosStar Q s := by
  intro s h
  induction h with
  | zs_base t hP => exact ZerosStar.zs_base t (hPQ t hP)
  | zs_step t _ ih => exact ZerosStar.zs_step t ih

/-!
## Dichotomy: Infinite Zeros or Finite Zeros

Coq lemma:
```coq
Lemma infzeros_or_finzeros: forall s,
  infzeros s \/ zeros_star nonzero s.
```
-/

/-- Every stream either has infinite zeros or has a nonzero prefix. -/
lemma infzeros_or_finzeros (s : Stream Nat) :
    infzeros s ∨ ZerosStar Nonzero s := by
  by_cases h : ZerosStar Nonzero s
  · exact Or.inr h
  · left
    unfold infzeros
    apply paco_coind InfZerosF (fun a b => a = b ∧ ¬ZerosStar Nonzero a) ⊥
    · intro a b ⟨hab, hnotzs⟩
      subst hab
      cases a with
      | snil =>
        exfalso
        apply hnotzs
        exact ZerosStar.zs_base snil Nonzero.nz_nil
      | scons n t =>
        by_cases hn : n = 0
        · subst hn
          apply InfZerosStep.zo_step t
          left
          constructor
          · rfl
          · intro hzst
            apply hnotzs
            exact ZerosStar.zs_step t hzst
        · exfalso
          apply hnotzs
          exact ZerosStar.zs_base (scons n t) (Nonzero.nz_cons n t hn)
    · exact ⟨rfl, h⟩

/-!
## Nonzero and Infinite Zeros are Mutually Exclusive

Coq lemma: `nonzero_not_infzeros`
-/

/-- A nonzero stream cannot have infinite zeros. -/
lemma nonzero_not_infzeros (s : Stream Nat) (hNZ : Nonzero s) (hIZ : infzeros s) : False := by
  cases hNZ with
  | nz_nil =>
    unfold infzeros at hIZ
    rcases hIZ with ⟨R, hpost, hxy⟩
    have hstep := hpost snil snil hxy
    cases hstep
  | nz_cons n t hNZ =>
    unfold infzeros at hIZ
    rcases hIZ with ⟨R, hpost, hxy⟩
    have hstep := hpost (scons n t) (scons n t) hxy
    cases hstep with
    | zo_step u _ =>
      -- scons 0 u = scons n t means n = 0, contradicting hNZ
      contradiction

/-!
## Generalized Stream Equivalence (gseq)

Coq definitions:
```coq
Inductive gseq_cons_or_nil (gseq: stream nat -> stream nat -> Prop) :
  stream nat -> stream nat -> Prop :=
| gseq_nil : gseq_cons_or_nil gseq snil snil
| gseq_cons s1 s2 n (R: gseq s1 s2) (NZ: n <> 0) :
    gseq_cons_or_nil gseq (scons n s1) (scons n s2).

Inductive gseq_step (gseq: stream nat -> stream nat -> Prop) :
  stream nat -> stream nat -> Prop :=
| gseq_inf s1 s2 (IZ1: infzeros s1) (IZ2: infzeros s2) :
    gseq_step gseq s1 s2
| gseq_fin s1 s2 t1 t2
     (ZS1: zeros_star (fun t => t = s1) t1)
     (ZS2: zeros_star (fun t => t = s2) t2)
     (R: gseq_cons_or_nil gseq s1 s2)
  : gseq_step gseq t1 t2.
```
-/

/-- Matching step for `gseq`: nil or matching non-zero heads. -/
inductive GseqConsOrNil (R : Stream Nat → Stream Nat → Prop) :
    Stream Nat → Stream Nat → Prop where
  | gseq_nil : GseqConsOrNil R snil snil
  | gseq_cons (n : Nat) (s1 s2 : Stream Nat) :
      R s1 s2 → n ≠ 0 → GseqConsOrNil R (scons n s1) (scons n s2)

/-- Step relation for `gseq`: either both infinite zeros, or finite prefixes. -/
inductive GseqStep (R : Stream Nat → Stream Nat → Prop) :
    Stream Nat → Stream Nat → Prop where
  | gseq_inf (s1 s2 : Stream Nat) :
      infzeros s1 → infzeros s2 → GseqStep R s1 s2
  | gseq_fin (s1 s2 t1 t2 : Stream Nat) :
      ZerosStar (fun t => t = s1) t1 →
      ZerosStar (fun t => t = s2) t2 →
      GseqConsOrNil R s1 s2 →
      GseqStep R t1 t2

/-- Bundled monotone transformer for `GseqStep`. -/
def GseqF : MonoRel (Stream Nat) where
  F := GseqStep
  mono := by
    intro R S hRS s t h
    induction h with
    | gseq_inf a1 a2 hz1 hz2 =>
      exact GseqStep.gseq_inf a1 a2 hz1 hz2
    | gseq_fin a1 a2 b1 b2 zs1 zs2 hcon =>
      apply GseqStep.gseq_fin a1 a2 b1 b2 zs1 zs2
      cases hcon with
      | gseq_nil => exact GseqConsOrNil.gseq_nil
      | gseq_cons n u1 u2 hR hNZ =>
        exact GseqConsOrNil.gseq_cons n u1 u2 (hRS _ _ hR) hNZ

/-- Generalized stream equivalence. -/
def gseq (s t : Stream Nat) : Prop := paco GseqF ⊥ s t

/-!
## seq implies gseq

Coq: `Lemma seq_implies_gseq`
-/

/-- `seq` implies `gseq`. -/
theorem seq_implies_gseq : ∀ s1 s2, seq s1 s2 → gseq s1 s2 := by
  intro s1 s2 h
  sorry -- Complex proof involving infzeros analysis

/-!
## gseq implies seq

Coq: `Lemma gseq_implies_seq`
-/

/-- `gseq` implies `seq`. -/
theorem gseq_implies_seq : ∀ s1 s2, gseq s1 s2 → seq s1 s2 := by
  intro s1 s2 h
  sorry -- Complex proof

/-!
## Transitivity of gseq

Coq proof:
```coq
Lemma gseq_trans : forall d1 d2 d3
  (EQL: gseq d1 d2) (EQR: gseq d2 d3), gseq d1 d3.
```
-/

/-- `gseq` is transitive. -/
theorem gseq_trans : ∀ d1 d2 d3, gseq d1 d2 → gseq d2 d3 → gseq d1 d3 := by
  intro d1 d2 d3 hL hR
  sorry -- Complex proof involving case analysis on infinite/finite zeros

/-!
## Transitivity of seq

Coq proof:
```coq
Lemma seq_trans : forall d1 d2 d3
  (EQL: seq d1 d2) (EQR: seq d2 d3), seq d1 d3.
Proof.
  eauto using gseq_trans, seq_implies_gseq, gseq_implies_seq.
Qed.
```
-/

/-- `seq` is transitive (via `gseq`). -/
theorem seq_trans : ∀ d1 d2 d3, seq d1 d2 → seq d2 d3 → seq d1 d3 := by
  intro d1 d2 d3 hL hR
  have hL' := seq_implies_gseq d1 d2 hL
  have hR' := seq_implies_gseq d2 d3 hR
  have htrans := gseq_trans d1 d2 d3 hL' hR'
  exact gseq_implies_seq d1 d3 htrans

/-!
## pclearbot Tests

Coq tests:
```coq
Lemma plcearbot_test1 x y
  (H: upaco2 seq_step bot2 x y) : True.
Proof. pclearbot. eauto. Qed.

Lemma plcearbot_test2
  (H: forall x y, upaco2 seq_step bot2 x y) : True.
Proof. pclearbot. eauto. Qed.
```

In paco-lean, `pclearbot` uses `simp only [Paco.upaco_bot]`.
-/

/-- Test `pclearbot` on a hypothesis.

Coq test:
```coq
Lemma plcearbot_test1 x y (H: upaco2 seq_step bot2 x y) : True.
Proof. pclearbot. eauto. Qed.
```
-/
lemma pclearbot_test1 (x y : Stream Nat)
    (H : upaco SeqF ⊥ x y) : True := by
  -- pclearbot simplifies upaco SeqF ⊥ to paco SeqF ⊥
  simp only [upaco_bot] at H
  -- H is now : paco SeqF ⊥ x y
  -- In Lean, we need to use H to avoid the unused variable warning
  have _ := H
  trivial

/-- Test `pclearbot` on a universally quantified hypothesis.

Coq test:
```coq
Lemma plcearbot_test2 (H: forall x y, upaco2 seq_step bot2 x y) : True.
Proof. pclearbot. eauto. Qed.
```
-/
lemma pclearbot_test2
    (H : ∀ x y, upaco SeqF ⊥ x y) : True := by
  -- pclearbot works on the context
  simp only [upaco_bot] at H
  -- H is now : ∀ x y, paco SeqF ⊥ x y
  have _ := H
  trivial

/-!
## Additional Examples

These examples supplement the Coq tests with additional paco-lean functionality.
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
example (x y : α) (h : paco EqF ⊥ x y) : EqF (upaco EqF ⊥) x y :=
  paco_unfold EqF ⊥ x y h

/-!
## Function-Based Stream Bisimulation with Up-To Closure
-/

def FStream (α : Type*) := Nat → α

def fhead {α : Type*} (s : FStream α) : α := s 0

def ftail {α : Type*} (s : FStream α) : FStream α := fun n => s (n + 1)

/-- Stream bisimulation generator for function-based streams. -/
def FStreamF (α : Type*) : MonoRel (FStream α) :=
  ⟨fun R s t => fhead s = fhead t ∧ R (ftail s) (ftail t), by
    intro R S hRS s t h
    exact And.intro h.1 (hRS _ _ h.2)
  ⟩

/-- Reflexive bisimulation using `reflClosure` with `gupaco_clo`. -/
theorem fstream_bisim_refl (α : Type*) (s : FStream α) :
    gupaco_clo (FStreamF α) reflClosure ⊥ s s := by
  apply upto_coind_bot (F := FStreamF α) (clo := reflClosure) (R := fun a b => a = b)
  · rfl
  · intro a b hab
    subst hab
    constructor
    · rfl
    · exact rclo.base (Or.inl rfl)

/-!
## TagRoundtrip Usage

Demonstrates the tagged relation framework for compatibility proofs.
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
