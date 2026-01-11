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

Optional integration with QPF/ITree lives in a separate package (see `paco-qpf`). The core paco library itself is QPF-agnostic.

## Separation of concerns

This package is **generic** and should remain independent of QPF/ITree:
- **In scope**: relations, monotone transformers, paco/upaco/gpaco, up-to, companion
- **Out of scope**: QPF types, ITree, domain-specific bisimulation proofs

If you want paco-based proofs for QPF/ITree, use the integration package `paco-qpf`.

## Modules

The library is organized into core modules and up-to technique modules. See [Architecture Guide](docs/03-architecture.md) for detailed module descriptions.

- `Paco.Basic`: Core definitions (`paco`, `upaco`, `MonoRel`) and lemmas
- `Paco.GPaco`: Generalized paco with guarded parameters (`gpaco`, `gupaco`)
- `Paco.Tactic`: Tactics for ergonomic proofs (`pfold`, `punfold`, `pstep`, `pbase`, etc.)
- `Paco.Coind`: Ergonomic coinduction wrappers (`coind`, `gcoind`, `upto_coind`)
- `Paco.UpTo`: Up-to techniques with closure operators (`rclo`, `Compatible`, `gpaco_clo`)
- `Paco.Companion`: Companion construction (greatest compatible closure)

## Installation

Add to your `lakefile.lean`:

```lean
require paco from git
  "https://github.com/hxrts/paco-lean.git"@"main"
```

See [Setup Guide](docs/01-setup.md) for detailed setup instructions including Nix flake support.

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
| `cloMono_union` | Union of monotone closures is monotone |
| `wcompat_union` | Union of weakly compatible closures is weakly compatible |
| `prespect_compatible'_tagged` | `PRespectful` plus `TagRoundtrip` and `PrespectRightGuarded` yields `Compatible'` for `prespectClosure` |
| `prespect_compatible'_strong` | `PRespectfulStrong` yields `Compatible'` for `prespectClosure` |
| `prespect_compatible'_inflationary` | `PRespectfulStrong` plus `Inflationary F` yields `Compatible'` via right-guardedness |
| `companion_compose` | Companion closed under composition (assumes transClosure compatible) |

## Production guarantees

This section summarizes which results are available without extra assumptions and which rely on additional conditions.

Guaranteed without extra assumptions:
- Core `paco`, `upaco`, and `gpaco` definitions with unfold and fold lemmas.
- Coinduction principles in `Paco.Coind` and `Paco.GPaco`.
- Soundness for closures that are proven `Compatible` or `Compatible'` in the library.

Guaranteed with additional assumptions:
- `prespect_compatible'_tagged` when `PRespectful`, `TagRoundtrip`, and `PrespectRightGuarded` are available.
- `prespect_compatible'_strong` when `PRespectfulStrong` is available.
- `prespect_compatible'_inflationary` when `PRespectfulStrong` and `Inflationary F` are available.

## Documentation

- [Setup Guide](docs/01-setup.md)
- [Theoretical Foundations](docs/02-theory.md)
- [Architecture Guide](docs/03-architecture.md)
- [Basic Usage Tutorial](docs/04-basic-usage.md)
- [GPaco & Guards Tutorial](docs/05-gpaco-guide.md)
- [Up-To Techniques Guide](docs/06-upto-guide.md)
- [Differences from Coq Paco](docs/07-coq-differences.md)

## References

- [The Power of Parameterization in Coinductive Proof (POPL 2013)](https://plv.mpi-sws.org/paco/)
- [An Equational Theory for Weak Bisimulation via Generalized Parameterized Coinduction (CPP 2020)](https://paulhe.com/assets/gpaco.pdf)
- [Interaction Trees (POPL 2020)](https://github.com/DeepSpec/InteractionTrees)

## License

[Apache 2.0](LICENSE)
