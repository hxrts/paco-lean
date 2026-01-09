# Basic Usage Tutorial

This tutorial teaches you to write coinductive proofs using paco. It assumes familiarity with the concepts in [Theoretical Foundations](02-theory.md).

## Defining a Monotone Transformer

Every paco proof starts with a monotone relation transformer. The transformer specifies the one-step behavior of your coinductive relation.

```lean
import Paco

def EqF : Paco.MonoRel α :=
  ⟨fun R x y => x = y ∨ R x y, by
    intro R S hRS x y hxy
    cases hxy with
    | inl heq => exact Or.inl heq
    | inr hR => exact Or.inr (hRS x y hR)
  ⟩
```

This transformer relates x and y if they are equal or if R relates them. The monotonicity proof shows that enlarging R enlarges the output. The `inl` case handles equality. The `inr` case uses the hypothesis that `R ≤ S`.

## Simple Coinduction

The `paco_coind` theorem is the main coinduction principle. It takes a witness relation R and shows `paco F r x y` when R is a post-fixpoint containing (x, y).

```lean
theorem paco_eq (x : α) : paco EqF ⊥ x x := by
  apply paco_coind EqF (fun a b => a = b) ⊥
  · intro a b hab
    subst hab
    simp only [Rel.sup_bot]
    exact Or.inl rfl
  · rfl
```

The first argument after `EqF` is the witness relation. Here it is equality. The second argument is the accumulator, which is `⊥` for proofs without accumulation. The first goal shows the witness is a post-fixpoint. The second goal shows the witness contains (x, x).

## Using the Coind Wrapper

The `coind` wrapper from `Paco.Coind` simplifies the interface. It reorders arguments and handles the `⊥` accumulator case.

```lean
theorem paco_eq' (x : α) : paco EqF ⊥ x x := by
  apply coind (R := fun a b => a = b)
  · rfl
  · intro a b hab
    subst hab
    exact Or.inl rfl
```

The witness comes first, then the membership proof, then the step function. The step function does not need the `⊔ r` part since the accumulator is handled internally.

## Working with the Accumulator

When you have facts to accumulate, use `coind_acc`. The step function receives `R ⊔ r` as the recursive relation.

```lean
theorem paco_with_acc (x : α) (r : Rel α) (hr : r x x) : paco EqF r x x := by
  apply coind_acc (R := fun a b => a = b)
  · rfl
  · intro a b hab
    subst hab
    exact Or.inl rfl
```

The accumulator `r` appears in the goal type. The step function can use facts from r by returning them on the right side of the disjunction.

## Using Tactics

The tactic interface provides commands that mirror the Coq paco library.

### pfold

The `pfold` tactic transforms a goal of `paco F r x y` into `F (upaco F r) x y`.

```lean
theorem test_pfold (x : α) : paco EqF ⊥ x x := by
  pfold
  exact Or.inl rfl
```

After `pfold`, the goal becomes `EqF (upaco EqF ⊥) x x`. The transformer expects either equality or a recursive call through upaco.

### pstep

The `pstep` tactic moves into the paco side of upaco. It transforms `upaco F r x y` into `F (upaco F r) x y`.

```lean
theorem test_pstep (x : α) : upaco EqF ⊥ x x := by
  pstep
  exact Or.inl rfl
```

Use `pstep` when you need to make progress on a upaco goal.

### pbase

The `pbase` tactic uses the accumulator side of upaco. It transforms `upaco F r x y` into `r x y`.

```lean
theorem test_pbase (x y : α) (hr : r x y) : upaco EqF r x y := by
  pbase
  exact hr
```

Use `pbase` when you can discharge the goal using accumulated facts.

### pclearbot

The `pclearbot` tactic simplifies `upaco F ⊥` to `paco F ⊥`.

```lean
theorem test_pclearbot (x y : α) (h : paco EqF ⊥ x y) : upaco EqF ⊥ x y := by
  pclearbot
  exact h
```

This is useful when the accumulator is empty and you have a paco hypothesis.

## Unfolding Hypotheses

The `paco_unfold` theorem exposes the F-structure inside a paco hypothesis.

```lean
example (x y : α) (h : paco EqF ⊥ x y) : EqF (upaco EqF ⊥) x y :=
  paco_unfold EqF ⊥ x y h
```

After unfolding, you can case split on the disjunction to handle equality and recursive cases separately.

## Example: Reflexivity

This complete example proves that `paco EqF ⊥` is reflexive.

```lean
theorem paco_refl (x : α) : paco EqF ⊥ x x := by
  pfold
  left
  rfl
```

The proof folds into paco, then provides the left disjunct (equality) with `rfl`.

## Next Steps

See [GPaco & Guards Tutorial](05-gpaco-guide.md) for two-parameter coinduction. See [Up-To Techniques Guide](06-upto-guide.md) for enhanced reasoning with closures.
