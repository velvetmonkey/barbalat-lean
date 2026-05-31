import Mathlib
import BarbalatLean.Barbalat

/-!
# Lyapunov-Barbalat Theorem

We prove the Lyapunov-Barbalat theorem: if `V` is a differentiable Lyapunov function
bounded below by `0` and `V'(t) ≤ -φ(t)` for `t ≥ 0`, with `φ` nonnegative and
uniformly continuous on `[0, ∞)`, then `φ(t) → 0` as `t → ∞`.
-/

open MeasureTheory Set Filter Topology

/-! ## Helper lemma: integral inequality from derivative bound -/

/-- If `V` is differentiable, `V' ≤ -φ` on `[0, ∞)`, and `φ` is continuous on `[0, ∞)`, then
`∫₀^T φ ≤ V(0) - V(T)` for all `T ≥ 0`.

*Proof:* Define `W(t) = ∫₀^t (-φ(s)) ds - V(t) + V(0)`. Then `W(0) = 0` and
`W'(t) = -φ(t) - V'(t) ≥ 0`, so `W` is nondecreasing. Hence `W(T) ≥ 0`. -/
lemma integral_phi_le (V φ : ℝ → ℝ)
    (hV_diff : Differentiable ℝ V)
    (hV' : ∀ t, 0 ≤ t → deriv V t ≤ -φ t)
    (hφ_cont : ContinuousOn φ (Set.Ici 0))
    {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, φ t ≤ V 0 - V T := by
  set W : ℝ → ℝ := fun t => (∫ s in (0 : ℝ)..t, -φ s) - V t + V 0;
  have hW_deriv : ∀ t ∈ Set.Ioo 0 T, HasDerivAt W (-φ t - deriv V t) t := by
    intro t ht
    have hW_deriv : HasDerivAt (fun t => ∫ s in (0 : ℝ)..t, -φ s) (-φ t) t := by
      apply_rules [ intervalIntegral.integral_hasDerivAt_right ];
      · apply_rules [ ContinuousOn.intervalIntegrable ];
        exact ContinuousOn.neg ( hφ_cont.mono ( by rw [ uIcc_of_le ht.1.le ] ; exact Set.Icc_subset_Ici_self ) );
      · exact ⟨ Set.Ioo 0 T, Ioo_mem_nhds ht.1 ht.2, ContinuousOn.aestronglyMeasurable ( by exact ContinuousOn.neg ( hφ_cont.mono ( Set.Ioo_subset_Icc_self.trans ( Set.Icc_subset_Ici_self ) ) ) ) measurableSet_Ioo ⟩;
      · exact ContinuousAt.neg ( hφ_cont.continuousAt ( Ici_mem_nhds ht.1 ) );
    convert HasDerivAt.add ( HasDerivAt.sub hW_deriv ( hV_diff.differentiableAt.hasDerivAt ) ) ( hasDerivAt_const _ _ ) using 1 ; ring;
  have hW_monotone : MonotoneOn W (Set.Icc 0 T) := by
    apply_rules [ monotoneOn_of_deriv_nonneg ];
    · exact convex_Icc _ _;
    · refine' ContinuousOn.add ( ContinuousOn.sub _ hV_diff.continuous.continuousOn ) continuousOn_const;
      intro t ht; apply_rules [ intervalIntegral.continuousWithinAt_primitive, ContinuousOn.intervalIntegrable ] ; aesop;
      simpa [ hT ] using hφ_cont.neg.mono ( Set.Icc_subset_Ici_self );
    · exact fun t ht => ( hW_deriv t <| by aesop ) |> HasDerivAt.differentiableAt |> DifferentiableAt.differentiableWithinAt;
    · intro t ht; rw [ hW_deriv t ( by simpa [ hT ] using ht ) |> HasDerivAt.deriv ] ; linarith [ hV' t ( by linarith [ Set.mem_Icc.mp ( interior_subset ht ) ] ) ] ;
  simp +zetaDelta at *;
  have := hW_monotone ( show 0 ∈ Set.Icc 0 T by norm_num; linarith ) ( show T ∈ Set.Icc 0 T by norm_num; linarith ) hT; norm_num at this; linarith;

/-- **Lyapunov-Barbalat Theorem**: Given `V : ℝ → ℝ` differentiable and bounded below by `0`,
with `deriv V t ≤ -φ(t)` for all `t ≥ 0`, if `φ` is nonnegative and uniformly continuous on
`[0, ∞)`, then `φ(t) → 0` as `t → ∞`. -/
theorem lyapunov_barbalat (V φ : ℝ → ℝ)
    (hV_diff : Differentiable ℝ V)
    (hV_bdd : ∀ t, 0 ≤ t → 0 ≤ V t)
    (hV' : ∀ t, 0 ≤ t → deriv V t ≤ -φ t)
    (hφ_nn : ∀ t, 0 ≤ t → 0 ≤ φ t)
    (hφ_uc : UniformContinuousOn φ (Set.Ici 0)) :
    Filter.Tendsto φ Filter.atTop (nhds 0) := by
  convert barbalat_nonneg φ hφ_uc ( fun t ht => hφ_nn t ht ) _;
  refine' ⟨ _, V 0, _ ⟩;
  · intro T hT; apply_rules [ ContinuousOn.intervalIntegrable ];
    simpa only [ Set.uIcc_of_le hT ] using hφ_uc.continuousOn.mono ( Set.Icc_subset_Ici_self );
  · intro T hT; rw [ Real.norm_of_nonneg ( intervalIntegral.integral_nonneg ( by linarith ) fun t ht => hφ_nn t ( by linarith [ ht.1 ] ) ) ] ; exact le_trans ( integral_phi_le V φ hV_diff hV' ( hφ_uc.continuousOn ) hT ) ( by linarith [ hV_bdd T hT ] ) ;
