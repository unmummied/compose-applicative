# The Composition of Functors/Applicatives Is Always a/an Functor/Applicative
A standalone formalization of Functor and Applicative laws for composed types.

## Features
- **Self-Implementation**
  Built from scratch using a `My`/`my` prefix, without relying on `namespace Hidden` or existing abstractions.
- **Different Approach from Mathlib4**
  Unlike the implementation in Mathlib4, this project assumes the **uniqueness of Functor instances as an axiom**, leading to a structurally different proof strategy.

## Verified Laws
- **Functor**
  - `id_map`
  - `comp_map`
- **Applicative**
  - `id_pure`
  - `map_pure`
  - `seq_pure`
  - `seq_assoc`
  - `pure_seq`
  - `shortcut` (a custom auxiliary law used in proofs)

## Build
```bash
lake build -v --log-level=warning
```
