# GPaco & Guards Tutorial

This tutorial explains generalized parametrized coinduction (gpaco). GPaco extends paco with a second parameter for guarded facts.

## When to Use GPaco

Use gpaco when you need to delay access to certain facts until after making progress. The guard prevents immediate use of facts that would create unsound reasoning.

Standard paco provides one parameter `r` for accumulated facts. GPaco provides two parameters: `r` for immediately available facts and `g` for guarded facts. Guarded facts become available only after one F-step.

## Available vs Guarded Parameters

The `gpaco F r g` relation has two parameters with different accessibility rules.

```lean
def gpaco (F : MonoRel α) (r g : Rel α) : Rel α :=
  paco F (r ⊔ g) ⊔ r
```

The parameter `r` is immediately available. You can use facts from `r` at any point. The parameter `g` is guarded. You must apply F once before accessing facts from `g`.

This distinction matters when certain facts would create circular reasoning if used immediately. The guard ensures you make progress before accessing them.

## Guard Release

The guard releases after one F-step. When you unfold a gpaco goal with `gpfold`, the recursive positions receive `gupaco F r g` instead of `gpaco F r g`.

```lean
def gupaco (F : MonoRel α) (r g : Rel α) : Rel α :=
  gpaco F r g ⊔ g
```

The `gupaco` definition adds `g` to the available facts. This equals `upaco F (r ⊔ g)`, meaning after one step both `r` and `g` are accessible.

```lean
theorem gupaco_eq_upaco (F : MonoRel α) (r g : Rel α) :
    gupaco F r g = upaco F (r ⊔ g)
```

The guard mechanism prevents using `g` before making progress. After the first F-step, the guard lifts and `g` joins the accumulator.

## Coinduction with GPaco

The `gpaco_coind` theorem provides coinduction for gpaco. The step function can return either an F-step or an immediate base case.

```lean
theorem gpaco_coind (F : MonoRel α) (R : Rel α) (r g : Rel α)
    (step : ∀ x y, R x y → F (R ⊔ gupaco F r g) x y ∨ r x y)
    {x y : α} (hxy : R x y) : gpaco F r g x y
```

The step function receives `R ⊔ gupaco F r g` for recursive calls. It can return `r x y` as a base case without making an F-step.

## The gcoind Wrapper

The `gcoind` wrapper from `Paco.Coind` provides a cleaner interface.

```lean
theorem gcoind {F : MonoRel α} {r g : Rel α} {x y : α}
    (R : Rel α)
    (witness : R x y)
    (step : ∀ a b, R a b → F (R ⊔ gupaco F r g) a b ∨ r a b) :
    gpaco F r g x y
```

The witness comes first, then the membership proof, then the step function.

## Tactics

The `gpfold` tactic transforms a goal of `gpaco F r g x y` into `F (gupaco F r g) x y ∨ r x y`.

```lean
theorem test_gpfold (x : α) : gpaco TestF ⊥ ⊥ x x := by
  gpfold
  exact Or.inl rfl
```

After `gpfold`, you choose between making an F-step (left disjunct) or using the base case (right disjunct).

## Relationship to Paco

GPaco generalizes paco. Several special cases reduce gpaco to simpler forms.

### Empty Guard

When the guard is empty, gpaco reduces to upaco.

```lean
theorem gpaco_bot_g (F : MonoRel α) (r : Rel α) :
    gpaco F r ⊥ = upaco F r
```

With no guarded facts, gpaco behaves exactly like upaco.

### Empty Available Parameter

When the available parameter is empty, gpaco reduces to paco.

```lean
theorem gpaco_bot_r (F : MonoRel α) (g : Rel α) :
    gpaco F ⊥ g = paco F g
```

With no base case, gpaco behaves like paco with the guard as accumulator.

### Diagonal Case

When both parameters are equal, gpaco simplifies.

```lean
theorem gpaco_diag (F : MonoRel α) (r : Rel α) :
    gpaco F r r = upaco F r
```

There is no distinction between available and guarded when they contain the same facts.

## Example: Multi-Step Proof

Consider proving a property that requires multiple F-steps with intermediate facts.

```lean
def StepF : MonoRel α :=
  ⟨fun R x y => x = y ∨ ∃ z, R x z ∧ R z y, by
    intro R S hRS x y hxy
    cases hxy with
    | inl heq => exact Or.inl heq
    | inr ⟨z, hxz, hzy⟩ => exact Or.inr ⟨z, hRS x z hxz, hRS z y hzy⟩
  ⟩
```

This transformer allows either equality or a two-step chain through an intermediate element.

Here is a complete proof using gpaco. The witness relation is equality, and the step function uses the left disjunct for the F-step.

```lean
theorem step_refl : gpaco StepF ⊥ ⊥ x x := by
  apply gpaco_coind StepF (fun a b => a = b) ⊥ ⊥
  · intro a b hab
    left
    subst hab
    exact Or.inl rfl
  · rfl
```

The proof chooses the F-step branch and provides equality. The guard and accumulator are both empty since no additional facts are needed.

## Accumulation with GPaco

GPaco supports accumulation similar to paco. The `gpaco_gupaco` theorem shows how gupaco absorbs into gpaco.

```lean
theorem gpaco_gupaco (F : MonoRel α) (r g : Rel α) :
    gpaco F (gupaco F r g) (gupaco F r g) ≤ gpaco F r g
```

This enables incremental proofs where intermediate gpaco results feed into subsequent arguments.

## Next Steps

See [Up-To Techniques Guide](06-upto-guide.md) for combining gpaco with closure operators.
