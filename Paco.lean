import Paco.Basic
import Paco.Companion
import Paco.GPaco
import Paco.Examples.Basic
import Paco.Tactic
import Paco.UpTo

/-!
# Parametrized Coinduction (Paco)

This module provides parametrized coinduction for Lean 4, enabling
compositional and incremental coinductive proofs.

## Overview

Paco solves the "accumulation problem" in coinductive proofs. Standard
coinduction requires providing a complete witness relation upfront, but
paco allows accumulating hypotheses as the proof progresses.

## Modules

- `Paco.Basic`: Core definitions (`paco`, `upaco`) and lemmas
- `Paco.GPaco`: Generalized paco with guarded parameters (`gpaco`, `gupaco`)
- `Paco.Tactic`: Tactics for ergonomic paco proofs
- `Paco.UpTo`: Up-to techniques with closure operators

## Usage

```lean
import Paco

-- Define a monotone relation transformer
def MyF : Paco.MonoRel MyType := ⟨fun R x y => ..., by ...⟩

-- Prove a coinductive property
theorem my_property : Paco.paco MyF ⊥ x y := by
  apply Paco.paco_coind MyF MyWitness ⊥
  · -- Show MyWitness is a post-fixpoint
    intro a b hab
    ...
  · -- Show MyWitness x y
    ...
```

## References

- [The Power of Parameterization in Coinductive Proof (POPL 2013)](https://plv.mpi-sws.org/paco/)
- [Paco Coq Library](https://github.com/snu-sf/paco)
-/
