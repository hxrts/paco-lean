# Paco: Parametrized Coinduction for Lean 4

A Lean 4 implementation of parametrized coinduction (paco), based on the [Coq paco library](https://github.com/snu-sf/paco).

## Overview

Paco solves the "accumulation problem" in coinductive proofs. Standard coinduction (Knaster-Tarski) requires providing a complete witness relation upfront:

```
gfp F = ⋃ { R | R ⊆ F(R) }
```

This makes some proofs difficult, especially transitivity where intermediate elements change at each step.

Paco parametrizes the fixed point:

```
paco F r = gfp (fun R => F(R ∪ r))
```

The parameter `r` accumulates facts during the proof and the coinductive hypothesis becomes `upaco F r = paco F r ∪ r`.

This package makes use of Alex C. Keizer's [Lean 4 formalization](https://github.com/alexkeizer/QpfTypes) of coinductive data types based on quotients of polynomial functors, which extends [foundational work](https://github.com/avigad/qpf) from Jeremy Avigad, Mario Carneiro, and Simon Hudon.

## Modules

- **`Paco.Basic`**: Core definitions (`paco`, `upaco`, `MonoRel`) and lemmas
- **`Paco.GPaco`**: Generalized paco with guarded parameters (`gpaco`, `gupaco`)
- **`Paco.Tactic`**: Tactics for ergonomic proofs (`pcofix`, `punfold`, `pfold`, etc.)
- **`Paco.UpTo`**: Up-to techniques with closure operators (`rclo`, `Compatible`, `gpaco_clo`)
- **`Paco.UpTo.GPacoClo`**: GPaco with user closures, companion (`cpn`), and coinduction/accumulation lemmas

## Installation

Add to your `lakefile.lean`:

```lean
require paco from git
  "https://github.com/YOUR_USERNAME/paco-lean.git"@"main"
```

## Usage

```lean
import Paco

-- Define a monotone relation transformer
def MyF : Paco.MonoRel MyType := ⟨fun R x y => ..., by ...⟩

-- Prove a coinductive property using paco_coind
theorem my_property : Paco.paco MyF ⊥ x y := by
  apply Paco.paco_coind MyF MyWitness ⊥
  · -- Show MyWitness is a post-fixpoint
    intro a b hab
    ...
  · -- Show MyWitness x y
    ...
```

## Key Theorems

| Theorem | Description |
|---------|-------------|
| `paco_mon` | paco is monotone in the parameter |
| `paco_unfold` | `paco F r ≤ F (upaco F r)` |
| `paco_fold` | `F (upaco F r) ≤ paco F r` |
| `paco_acc` | `paco F (paco F r) ≤ paco F r` (accumulation) |
| `paco_coind` | Main coinduction principle |
| `paco_bot` | `paco F ⊥ = gfp F` |
| `gpaco_clo_coind` | Coinduction principle for gpaco with closures |
| `gpaco_clo_gupaco` | Gupaco absorption into gpaco (accumulation) |

## References

- [Implementing a definitional (co)datatype package in Lean 4, based on quotients of polynomial functors](https://eprints.illc.uva.nl/id/eprint/2239/1/MoL-2023-03.text.pdf)
- [Datatypes as Quotients of Polynomial Functors](https://www.andrew.cmu.edu/user/avigad/Talks/qpf.pdf)
- [The Power of Parameterization in Coinductive Proof (POPL 2013)](https://plv.mpi-sws.org/paco/)
- [An Equational Theory for Weak Bisimulation via Generalized Parameterized Coinduction (CPP 2020)](https://paulhe.com/assets/gpaco.pdf)
- [Interaction Trees (POPL 2020)](https://github.com/DeepSpec/InteractionTrees)

## License

[Apache 2.0](LICENSE)
