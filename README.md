# Formalizing Functor/Applicative Composition in Lean 4
A standalone formalization of Functor and Applicative laws for composed types.

This project is a faithful implementation of Haskell's standard type class laws in Lean 4, rather than a re-implementation of Lean's Init.Prelude versions.

## Features
- **Different Approach from `mathlib4`**:
  Unlike the implementation in `mathlib4`, this project assumes the **uniqueness of Functor instances as an axiom**, leading to a structurally different proof strategy.

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
  - `pure_seq_pure_seq` (a custom auxiliary law used in proofs)

## Build
```bash
lake build -v --log-level=warning
```
