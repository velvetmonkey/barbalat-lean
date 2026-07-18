# barbalat-lean

[![Lean 4](https://img.shields.io/badge/Lean-4.28.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-purple)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Proofs](https://img.shields.io/badge/proofs-proven%20%2F%200%20sorry-brightgreen)](BarbalatLean)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20480607.svg)](https://doi.org/10.5281/zenodo.20480607)

**barbalat-lean: Formal Proofs of Barbalat's Lemma in Lean 4**

Lean 4 formal proofs of Barbalat's lemma and a Lyapunov-Barbalat corollary. The development covers uniformly continuous functions on `[0, infinity)`, integrability and bounded integral conditions on rays, convergence of functions to zero, and a Lyapunov derivative criterion for asymptotic convergence.

**Zero sorry statements.** Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).

## What this is, and why it matters

This library formalizes Barbalat's lemma, a tool used in stability theory and adaptive control. Its headline theorem, `lyapunov_barbalat`, proves that a nonnegative signal `phi` tends to zero when it is uniformly continuous and is dominated by the decrease of a differentiable, nonnegative Lyapunov function.

The proof matters because it machine-checks the bridge from an energy inequality to pointwise decay. A derivative bound gives an upper bound on the integral of `phi`; the formalized nonnegative Barbalat lemma then shows that a uniformly continuous signal with bounded accumulated mass cannot keep returning away from zero.

The scope is explicit. The theorem assumes differentiability of the Lyapunov function, its nonnegativity, the derivative inequality, and uniform continuity and nonnegativity of `phi` on the nonnegative real ray. It does not verify those conditions for a concrete dynamical system, and decay of `phi` alone is not a general state-convergence theorem.

## Background and motivation

Barbalat's lemma is a standard tool in stability theory and adaptive control. It converts a regularity assumption and an integral convergence condition into pointwise convergence to zero. Informally, if a uniformly continuous signal has finite accumulated mass on `[0, infinity)`, then it cannot keep making excursions away from zero.

The Lyapunov-Barbalat theorem is the corresponding stability corollary: if a nonnegative Lyapunov function satisfies `V'(t) <= -phi(t)` and `phi` is nonnegative and uniformly continuous, then `phi(t) -> 0`.

## Setting

The library works with real-valued functions on the real ray `[0, infinity)`.

Uniform continuity is represented by:

```text
UniformlyContinuousOn f (Set.Ici 0)
```

The ray-integrability condition packages interval integrability over `[0,T]` for all `T >= 0` together with a bounded interval integral:

```text
IntegrableOnRay f :=
  (forall T >= 0, IntervalIntegrable f volume 0 T)
  and exists M, forall T >= 0, || integral_0^T f || <= M
```

## Main Result

Barbalat's lemma:

```text
UniformlyContinuousOn f [0, infinity)
IntegrableOn f [0, infinity)
---------------------------------
Tendsto f atTop (nhds 0)
```

Lyapunov-Barbalat corollary:

```text
V differentiable
0 <= V(t)
deriv V(t) <= -phi(t)
0 <= phi(t)
phi uniformly continuous on [0, infinity)
-----------------------------------------
Tendsto phi atTop (nhds 0)
```

## Project structure

```text
BarbalatLean/
├── Defs.lean             — UniformlyContinuousOn and IntegrableOnRay
├── Barbalat.lean         — Barbalat's lemma and nonnegative variant
└── LyapunovBarbalat.lean — Integral inequality and Lyapunov-Barbalat theorem
BarbalatLean.lean         — Root module
```

## Theorem inventory

| # | Name | Statement |
|---|------|-----------|
| 1 | `iInter_Ici_nat_eq_empty` | The intersection of `Ici n` over all natural numbers is empty |
| 2 | `tail_norm_integral_tendsto` | The tail integral of `||f||` over `Ici n` tends to zero |
| 3 | `uc_norm_lower_bound` | Uniform continuity gives a local lower bound on `||f||` near any point where `||f|| >= epsilon` |
| 4 | `setIntegral_norm_ge_of_ge` | A pointwise lower bound on `||f||` over an interval gives a lower bound on the set integral |
| 5 | `setIntegral_norm_mono_set` | The integral of a nonnegative norm over a subset is bounded by the integral over a superset |
| 6 | `barbalat_lemma` | Uniform continuity on `[0, infinity)` plus integrability on the ray implies `f(t) -> 0` |
| 7 | `barbalat_nonneg` | Nonnegative uniformly continuous functions satisfying `IntegrableOnRay` tend to zero |
| 8 | `integral_phi_le` | If `V' <= -phi`, then `integral_0^T phi <= V(0) - V(T)` |
| 9 | `lyapunov_barbalat` | The Lyapunov-Barbalat theorem: under the derivative and uniform-continuity hypotheses, `phi(t) -> 0` |

## Dependencies

- Lean 4.28.0
- Mathlib v4.28.0

## Related work

- [lyapunov-odes-lean](https://github.com/velvetmonkey/lyapunov-odes-lean) — Lean 4 Lyapunov arguments for ODEs
- [lasalle-lean](https://github.com/velvetmonkey/lasalle-lean) — Lean 4 LaSalle invariance principles
- [contraction-lean](https://github.com/velvetmonkey/contraction-lean) — Lean 4 contraction and convergence reasoning

## Acknowledgements

Proofs in this library were generated using [Aristotle](https://aristotle.harmonic.fun), an AI proof assistant for Lean 4 and Mathlib. The proof discipline — zero sorry, standard axioms only — was specified by the author and enforced by the Lean type checker.

## Author

Ben Cassie · [@thevelvetmonke](https://x.com/thevelvetmonke)
## Part of the Lean proof corpus

One of a family of small, machine-checked Lean 4 developments. Index: [velvetmonkey/lean](https://github.com/velvetmonkey/lean) ([live index](https://velvetmonkey.github.io/lean)).
