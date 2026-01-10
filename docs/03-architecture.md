# Architecture Guide

This document describes the module structure and design decisions of paco-lean.

## Module Overview

The library is organized into core modules and up-to technique modules. Core modules provide parametrized coinduction without closure operators. Up-to modules extend this with enhanced reasoning capabilities.

```
Paco.lean (root)
├── Paco/Basic.lean      -- Core definitions
├── Paco/GPaco.lean      -- Generalized paco
├── Paco/Tactic.lean     -- Proof tactics
├── Paco/Companion.lean  -- Companion construction
├── Paco/Compat.lean     -- Coq naming aliases
├── Paco/Coind.lean      -- Coinduction wrappers
├── Paco/Simp.lean       -- Simp lemmas
├── Paco/Examples/       -- Example proofs
└── Paco/UpTo/           -- Up-to techniques
    ├── Rclo.lean        -- Reflexive closure
    ├── Compat.lean      -- Compatibility
    ├── Cpn.lean         -- Companion
    ├── GPacoClo.lean    -- GPaco with closures
    ├── WCompat.lean     -- Weak compatibility
    ├── Closures.lean    -- Standard closures
    └── Compose.lean     -- Closure composition
```

Import `Paco` to get all functionality. Individual modules can be imported for smaller dependency footprints.

## Core Modules

### Paco/Basic.lean

This module defines the fundamental types and operations. The `Rel α` type represents binary relations as functions `α → α → Prop`. Relations form a complete lattice with union as join and intersection as meet.

```lean
def Rel (α : Type*) := α → α → Prop
```

The lattice operations use pointwise definitions. The bottom element `⊥` is the empty relation. The top element `⊤` is the total relation.

The `MonoRel α` type bundles a relation transformer with a monotonicity proof. This bundling ensures all transformers used with paco satisfy the required property.

```lean
structure MonoRel (α : Type*) where
  toFun : Rel α → Rel α
  mono : Monotone toFun
```

The `paco` and `upaco` definitions are the core of parametrized coinduction. They are defined using an existential witness characterization rather than directly as fixed points.

### Paco/GPaco.lean

This module extends paco with a second parameter for guarded facts. The `gpaco F r g` definition represents generalized parametrized coinduction. The `gupaco F r g` definition provides the usable coinductive hypothesis.

Key theorems connect gpaco to paco. When the guard is empty or equals the accumulator, gpaco simplifies.

### Paco/Tactic.lean

This module provides tactics that mirror the Coq paco library. The `pfold` tactic folds an F-step into paco. The `punfold` tactic unfolds paco to expose F.

The `pstep` tactic moves into the paco side of upaco. The `pbase` tactic uses the accumulator side. The `pclearbot` tactic simplifies `upaco F ⊥` to `paco F ⊥`.

### Paco/Coind.lean

This module provides ergonomic wrappers for coinduction. The `coind` theorem hides plumbing for simple proofs. The `coind_acc` theorem handles accumulators.

For gpaco and up-to reasoning, `gcoind`, `upto_coind`, and `companion_coind` provide entry points with reduced boilerplate.

### Paco/Compat.lean

This module provides naming aliases for users familiar with the Coq paco library. It maps Coq names to their Lean equivalents.

| Coq Name           | Lean Name          | Description                     |
|--------------------|--------------------|---------------------------------|
| `paco_mult`        | `paco_acc`         | `paco F (paco F r) ≤ paco F r`  |
| `paco_mult_strong` | `paco_acc_upaco`   | `paco F (upaco F r) ≤ paco F r` |
| `gpaco_mult`       | `gpaco_clo_gupaco` | Gupaco absorption               |

### Paco/Simp.lean

This module defines additional simp lemmas for common simplifications. These supplement the core lemmas marked with `@[simp]` in other modules.

## Up-To Modules

### Paco/UpTo/Rclo.lean

This module defines `rclo`, the reflexive-transitive closure under a closure operator. The definition uses an inductive type with base case and closure application.

```lean
inductive rclo (clo : Rel α → Rel α) (R : Rel α) : Rel α where
  | base : R x y → rclo clo R x y
  | clo : clo (rclo clo R) x y → rclo clo R x y
```

This construction allows iterating a closure while accumulating results.

### Paco/UpTo/Compat.lean

This module defines compatibility between transformers and closures. A closure is compatible with F when `clo (F R) ≤ F (clo R)`.

```lean
def Compatible (F : MonoRel α) (clo : Rel α → Rel α) : Prop :=
  ∀ R, clo (F R) ≤ F (clo R)
```

Compatibility ensures the closure preserves the F-structure needed for soundness.

### Paco/UpTo/Cpn.lean

This module constructs the companion as a supremum over compatible monotone closures. The companion is the greatest closure satisfying both monotonicity and compatibility.

### Paco/UpTo/GPacoClo.lean

This module defines gpaco with user-provided closures. The `gpaco_clo F clo r rg` definition composes F with `rclo clo`. Key theorems include coinduction principles and accumulation.

### Paco/UpTo/WCompat.lean

This module provides weak compatibility, a relaxed notion using gupaco instead of paco. Weak compatibility is easier to establish for some closures.

### Paco/UpTo/Closures.lean

This module defines standard closure operators. These include `reflClosure`, `symmClosure`, `transClosure`, `rtClosure`, and `eqvClosure`.

### Paco/UpTo/Compose.lean

This module proves composition lemmas for closures. Composing compatible closures yields a compatible closure. Idempotence lemmas simplify nested applications.

## Key Types

### Rel α

Binary relations are the fundamental data type. All paco operations work on relations. The lattice structure provides union, intersection, and subset ordering.

### MonoRel α

Bundled monotone transformers ensure well-formedness. The `toFun` field gives the transformer. The `mono` field proves monotonicity.

### rclo clo R

Reflexive closure under a closure operator. This type accumulates closure applications starting from base relation R.

## Design Decisions

### Bundled Monotone Transformers

The `MonoRel` type bundles transformers with monotonicity proofs. This prevents errors from passing non-monotone functions to paco. The alternative of requiring monotonicity at each use site would create proof obligations throughout client code.

### Separation from QPF/ITree

The library is independent of QPF and ITree. This keeps the core small and avoids heavy dependencies. Integration with specific coinductive types belongs in separate packages like paco-qpf.

### Simp Lemma Strategy

Some lemmas are marked `@[simp]` while others are not. The `paco_eq` and `gpaco_step` lemmas can cause simp loops and are not marked. Lemmas that always reduce complexity are marked.
