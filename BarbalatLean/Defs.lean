import Mathlib

/-!
# Definitions for Barbalat's Lemma library

This file defines:
- `UniformlyContinuousOn` — a wrapper around Mathlib's `UniformContinuousOn`
- `IntegrableOnRay` — integrability on `[0, T]` for all `T` with bounded integral
-/

open MeasureTheory Set Filter Topology

/-- `f` is uniformly continuous on `s`, defined via Mathlib's `UniformContinuousOn`. -/
def UniformlyContinuousOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  UniformContinuousOn f s

/-- `f` is integrable on every interval `[0, T]` and the interval integral `∫₀^T f(t) dt`
is bounded as `T → ∞`. -/
def IntegrableOnRay (f : ℝ → ℝ) : Prop :=
  (∀ T : ℝ, 0 ≤ T → IntervalIntegrable f MeasureTheory.volume 0 T) ∧
    ∃ M : ℝ, ∀ T : ℝ, 0 ≤ T → ‖∫ t in (0 : ℝ)..T, f t‖ ≤ M
