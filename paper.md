# barbalat-lean: Formal Proofs of Barbalat's Lemma in Lean 4

Ben Cassie  
ORCID: 0009-0004-1899-7627  
DOI: 10.5281/zenodo.20480607  
2026-05-31

## Abstract

`barbalat-lean` is a Lean 4 / Mathlib library formalising Barbalat's lemma and a Lyapunov-Barbalat corollary for real-valued functions on the ray `[0, infinity)`. The development defines uniform continuity on a set, an integrability-on-a-ray condition, helper lemmas about tail integrals and local lower bounds, the main Barbalat convergence theorem, a nonnegative variant, and a Lyapunov derivative criterion. The proof method combines uniform continuity with finite accumulated integral mass to rule out persistent excursions away from zero. The library is machine-checked in Lean 4 with zero `sorry`, zero `admit`, and standard Lean/Mathlib axioms only.

## 1. Introduction

Barbalat's lemma is a standard result in stability theory and adaptive control. It says, informally, that a uniformly continuous signal with finite accumulated mass on the nonnegative time ray must converge to zero. This is useful because Lyapunov arguments often provide integral bounds rather than direct pointwise convergence.

The Lyapunov-Barbalat corollary converts a derivative inequality into asymptotic convergence. If a nonnegative Lyapunov function satisfies `V'(t) <= -phi(t)` and `phi` is nonnegative and uniformly continuous, then `phi(t)` tends to zero. The Lean library formalises this analytic proof pattern directly.

## 2. Mathematical Setting

`BarbalatLean/Defs.lean` defines

```text
UniformlyContinuousOn f s
```

for real-valued functions and sets, and

```text
IntegrableOnRay f
```

for functions that are interval-integrable on `[0,T]` for all `T >= 0` and whose interval integrals are bounded on the ray. The main theorems work with functions on `Set.Ici 0`, the nonnegative real ray.

`Barbalat.lean` proves the analytic helper lemmas and the main lemma. `LyapunovBarbalat.lean` proves the integral inequality obtained from `V' <= -phi` and combines it with the nonnegative Barbalat theorem.

## 3. Main Theorems

The helper theorem `tail_norm_integral_tendsto` proves that the tail integral of `||f||` tends to zero under the integrability hypotheses. The theorem `uc_norm_lower_bound` extracts a local interval on which `||f||` remains bounded below whenever it is large at a point. The measure-theoretic comparison lemmas `setIntegral_norm_ge_of_ge` and `setIntegral_norm_mono_set` turn this local lower bound into an integral lower bound.

The main theorem is `barbalat_lemma`:

```text
UniformlyContinuousOn f (Set.Ici 0)
IntegrableOnRay (fun t => ||f t||)
-----------------------------------
Tendsto f atTop (nhds 0).
```

The nonnegative variant `barbalat_nonneg` proves convergence for nonnegative uniformly continuous functions satisfying `IntegrableOnRay`.

The Lyapunov theorem `lyapunov_barbalat` states that if `V` is differentiable, `0 <= V(t)`, `deriv V(t) <= -phi(t)`, `0 <= phi(t)`, and `phi` is uniformly continuous on the ray, then

```text
Tendsto phi atTop (nhds 0).
```

## 4. Proof Sketch

The contradiction argument behind Barbalat's lemma is classical. If `f` does not tend to zero, then for some `epsilon > 0` there are arbitrarily late times where `||f|| >= epsilon`. Uniform continuity gives a fixed-width neighbourhood around each such time where `||f||` remains bounded below. Those neighbourhoods contribute a uniform positive amount to the tail integral. This contradicts the fact that the tail integral tends to zero.

The Lyapunov corollary first integrates the derivative inequality to obtain `integral_0^T phi <= V(0) - V(T)`. Nonnegativity of `V` bounds the integral of `phi` on the ray. Since `phi` is nonnegative and uniformly continuous, `barbalat_nonneg` applies and gives convergence to zero.

## 5. Relation to Sibling Libraries

`barbalat-lean` is part of the stability side of the suite. It is closest to `lyapunov-odes-lean`, DOI `10.5281/zenodo.20475912`, and `lasalle-lean`, DOI `10.5281/zenodo.20476034`, which formalise Lyapunov and invariance-principle reasoning. `contraction-lean`, DOI `10.5281/zenodo.20474762`, proves convergence through metric contraction. Together these repositories cover several common routes from local inequalities to asymptotic convergence.

## 6. Conclusion

`barbalat-lean` supplies a Lean 4 proof of Barbalat's lemma and a Lyapunov-Barbalat corollary. It formalises the uniform-continuity, tail-integral, and derivative-inequality components needed for the standard adaptive-control argument. Future work could connect this library to a richer ODE trajectory interface and use it to prove convergence of concrete feedback systems.

## References

Khalil, H. K. (2002). *Nonlinear Systems*. Prentice Hall.

Slotine, J.-J. E. and Li, W. (1991). *Applied Nonlinear Control*. Prentice Hall.

The Mathlib Community. (2024). *The Lean Mathematical Library*. GitHub repository. <https://github.com/leanprover-community/mathlib4>

Cassie, B. (2026). *lyapunov-odes-lean*. Zenodo. <https://doi.org/10.5281/zenodo.20475912>

Cassie, B. (2026). *lasalle-lean*. Zenodo. <https://doi.org/10.5281/zenodo.20476034>

Cassie, B. (2026). *contraction-lean*. Zenodo. <https://doi.org/10.5281/zenodo.20474762>
