import Mathlib
import BarbalatLean.Defs

/-!
# Barbalat's Lemma

We prove Barbalat's lemma: if `f : ℝ → ℝ` is uniformly continuous on `[0, ∞)` and
its integral over `[0, ∞)` is finite, then `f(t) → 0` as `t → ∞`.

We also prove a variant for nonnegative functions where the integral-bound condition
(`IntegrableOnRay`) suffices.
-/

open MeasureTheory Set Filter Topology

/-! ## Helper lemmas -/

/-- The intersection of `Ici n` over all natural numbers `n` is empty. -/
lemma iInter_Ici_nat_eq_empty : ⋂ n : ℕ, Set.Ici (↑n : ℝ) = ∅ := by
  exact Set.eq_empty_of_forall_notMem fun x hx => by
    rcases exists_nat_gt x with ⟨n, hn⟩
    exact absurd (Set.mem_iInter.mp hx n) (by norm_num; linarith)

/-- The tail integral of `‖f‖` on `Ici n` tends to `0` as `n → ∞`. This follows from
`Antitone.tendsto_setIntegral` applied to the norm. -/
lemma tail_norm_integral_tendsto (f : ℝ → ℝ)
    (hint : IntegrableOn f (Set.Ici 0)) :
    Filter.Tendsto (fun n : ℕ => ∫ x in Set.Ici (↑n : ℝ), ‖f x‖) Filter.atTop (nhds 0) := by
  convert (Antitone.tendsto_setIntegral (fun n => measurableSet_Ici)
    (fun n m hnm => ?_) ?_) using 2
  all_goals norm_num [iInter_Ici_nat_eq_empty]
  exacts [fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance, hnm,
    by exact MeasureTheory.Integrable.abs ‹_›]

/-- If `f` is uniformly continuous on `[0, ∞)` and `‖f t₀‖ ≥ ε` for some `t₀ ≥ 0`, then
`‖f t‖ ≥ ε / 2` for all `t` in a `δ`-neighborhood of `t₀` (within `[0, ∞)`). -/
lemma uc_norm_lower_bound (f : ℝ → ℝ)
    (huc : UniformContinuousOn f (Set.Ici 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ε ≤ ‖f t₀‖ →
      ∀ t, t₀ ≤ t → t ≤ t₀ + δ → ε / 2 ≤ ‖f t‖ := by
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ x ∈ Set.Ici 0, ∀ y ∈ Set.Ici 0,
      dist x y < δ → dist (f x) (f y) < ε / 2 :=
    Metric.uniformContinuousOn_iff.1 huc (ε / 2) (half_pos hε)
  refine ⟨δ / 2, half_pos hδ_pos, fun t₀ ht₀ hε₀ t ht₁ ht₂ => ?_⟩
  specialize hδ t₀ ht₀ t (by norm_num; linarith) (abs_lt.2 ⟨by linarith, by linarith⟩)
  simp_all +decide [dist_eq_norm]
  cases abs_cases (f t₀ - f t) <;> cases abs_cases (f t₀) <;> cases abs_cases (f t) <;> linarith

/-- Lower bound on the set integral of `‖f‖` over `[t₀, t₀ + δ]` when `‖f‖ ≥ c` there. -/
lemma setIntegral_norm_ge_of_ge (f : ℝ → ℝ) {t₀ δ c : ℝ}
    (hδ : 0 < δ) (_hc : 0 ≤ c) (_ht₀ : 0 ≤ t₀)
    (hf : ∀ t, t₀ ≤ t → t ≤ t₀ + δ → c ≤ ‖f t‖)
    (hfi : IntegrableOn f (Set.Icc t₀ (t₀ + δ))) :
    c * δ ≤ ∫ x in Set.Icc t₀ (t₀ + δ), ‖f x‖ := by
  refine' le_trans _ (MeasureTheory.setIntegral_mono_on _ _ measurableSet_Icc
    fun x hx => hf x hx.1 hx.2) <;> norm_num [mul_comm, hδ.le]
  exact hfi.norm

/-- Monotonicity: integral of a nonneg function on a subset is `≤` integral on a superset. -/
lemma setIntegral_norm_mono_set (f : ℝ → ℝ) {s t : Set ℝ}
    (hst : s ⊆ t)
    (hint : IntegrableOn f t) (_hs : MeasurableSet s) :
    ∫ x in s, ‖f x‖ ≤ ∫ x in t, ‖f x‖ := by
  apply_rules [MeasureTheory.setIntegral_mono_set]
  · exact MeasureTheory.Integrable.abs ‹_›
  · exact Filter.Eventually.of_forall fun x => norm_nonneg _
  · exact Filter.Eventually.of_forall hst

/-! ## Main theorems -/

/-- **Barbalat's Lemma**: If `f` is uniformly continuous on `[0, ∞)` and integrable on `[0, ∞)`,
then `f(t) → 0` as `t → ∞`. -/
theorem barbalat_lemma (f : ℝ → ℝ)
    (huc : UniformContinuousOn f (Set.Ici 0))
    (hint : IntegrableOn f (Set.Ici 0)) :
    Filter.Tendsto f Filter.atTop (nhds 0) := by
  by_contra h_contra
  -- Extract ε > 0 and a witness for "f doesn't tend to 0"
  obtain ⟨ε, hε⟩ : ∃ ε > 0, ∀ N : ℝ, ∃ t ≥ N, ε ≤ ‖f t‖ := by
    rw [Metric.tendsto_nhds] at h_contra; aesop
  -- Get δ from uniform continuity: ‖f t‖ ≥ ε/2 on [t₀, t₀ + δ] when ‖f t₀‖ ≥ ε
  obtain ⟨δ, hδ_pos, hδ⟩ := uc_norm_lower_bound f huc hε.1
  -- The tail integral of ‖f‖ goes to 0, so find N with tail < ε/2 * δ
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∫ x in Set.Ici (↑N : ℝ), ‖f x‖ < ε / 2 * δ := by
    have := tail_norm_integral_tendsto f ‹_›
    exact (this.eventually (gt_mem_nhds <| by nlinarith)) |> fun h => h.exists
  -- Pick t₀ ≥ N with ‖f t₀‖ ≥ ε
  obtain ⟨t₀, ht₀_ge_N, ht₀⟩ : ∃ t₀ : ℝ, N ≤ t₀ ∧ ε ≤ ‖f t₀‖ := hε.2 N
  -- Lower bound: ∫_{Icc t₀ (t₀+δ)} ‖f‖ ≥ (ε/2) * δ
  have h_integral_ge : ∫ x in Set.Icc t₀ (t₀ + δ), ‖f x‖ ≥ (ε / 2) * δ := by
    refine' le_trans _ (MeasureTheory.setIntegral_mono_on _ _ measurableSet_Icc
      fun x hx => hδ t₀ (by linarith) ht₀ x hx.1 hx.2) <;> norm_num [mul_comm, hδ_pos.le]
    exact MeasureTheory.IntegrableOn.mono_set
      (by exact MeasureTheory.Integrable.abs (by exact ‹IntegrableOn f (Set.Ici 0) volume›))
      (Set.Icc_subset_Ici_self.trans (Set.Ici_subset_Ici.2 <| by linarith))
  -- Upper bound: ∫_{Icc t₀ (t₀+δ)} ‖f‖ ≤ ∫_{Ici N} ‖f‖ < (ε/2) * δ
  have h_integral_le : ∫ x in Set.Icc t₀ (t₀ + δ), ‖f x‖ ≤ ∫ x in Set.Ici (↑N : ℝ), ‖f x‖ := by
    refine' MeasureTheory.setIntegral_mono_set _ _ _
    · exact MeasureTheory.IntegrableOn.mono_set
        (by exact MeasureTheory.Integrable.norm ‹_›)
        (Set.Ici_subset_Ici.mpr <| by linarith)
    · exact Filter.Eventually.of_forall fun x => norm_nonneg _
    · exact MeasureTheory.ae_of_all _ fun x hx => ht₀_ge_N.trans hx.1
  linarith

/-- **Barbalat's Lemma for nonnegative functions**: If `f ≥ 0` is uniformly continuous on
`[0, ∞)` and satisfies `IntegrableOnRay` (integral on `[0, T]` bounded as `T → ∞`),
then `f(t) → 0` as `t → ∞`. -/
theorem barbalat_nonneg (f : ℝ → ℝ)
    (huc : UniformContinuousOn f (Set.Ici 0))
    (hnn : ∀ t, 0 ≤ t → 0 ≤ f t)
    (hbdd : IntegrableOnRay f) :
    Filter.Tendsto f Filter.atTop (nhds 0) := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ T : ℝ, 0 ≤ T → ∫ t in (0 : ℝ)..T, f t ≤ M :=
    ⟨hbdd.2.choose, fun T hT => le_of_abs_le (hbdd.2.choose_spec T hT)⟩
  have h_monotone : MonotoneOn (fun T : ℝ => ∫ t in (0 : ℝ)..T, f t) (Set.Ici 0) := by
    intros T hT T' hT' hTT'
    apply_rules [intervalIntegral.integral_mono_interval, hT, hT']
    · norm_num
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht using hnn t ht.1.le
    · exact hbdd.1 T' hT'
  have h_lim : Filter.Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, f t) Filter.atTop
      (nhds (⨆ T : ℝ, ⨆ (_ : 0 ≤ T), ∫ t in (0 : ℝ)..T, f t)) := by
    rw [Filter.tendsto_atTop']
    intro s hs
    obtain ⟨ε, hε⟩ : ∃ ε > 0, Metric.ball (⨆ T : ℝ, ⨆ (_ : 0 ≤ T),
        ∫ t in (0 : ℝ)..T, f t) ε ⊆ s :=
      Metric.mem_nhds_iff.mp hs
    obtain ⟨T₀, hT₀⟩ : ∃ T₀ : ℝ, 0 ≤ T₀ ∧
        ∫ t in (0 : ℝ)..T₀, f t >
        (⨆ T : ℝ, ⨆ (_ : 0 ≤ T), ∫ t in (0 : ℝ)..T, f t) - ε := by
      contrapose! hε
      have h_sup_le : ⨆ T : ℝ, ⨆ (_ : 0 ≤ T), ∫ t in (0 : ℝ)..T, f t ≤
          (⨆ T : ℝ, ⨆ (_ : 0 ≤ T), ∫ t in (0 : ℝ)..T, f t) - ε := by
        refine' ciSup_le fun T => _
        rw [@ciSup_eq_ite]
        split_ifs <;> [exact hε _ ‹_›; exact le_trans (by norm_num) (hε 0 le_rfl)]
      grind +revert
    use T₀
    intro T hT
    refine' hε.2 (Metric.mem_ball.mpr _)
    rw [dist_eq_norm, Real.norm_of_nonpos] <;> norm_num
    · linarith [h_monotone hT₀.1 (show 0 ≤ T by linarith) hT]
    · refine' le_trans _ (le_ciSup _ T)
      · rw [ciSup_pos]; linarith
      · refine' ⟨Max.max M 0, Set.forall_mem_range.2 fun T => _⟩
        rw [@ciSup_eq_ite]; norm_num
        grind
  convert barbalat_lemma f huc _
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  rw [MeasureTheory.integrableOn_congr_fun (fun x hx => by rfl) measurableSet_Ioi]
  apply_rules [MeasureTheory.integrableOn_Ioi_deriv_of_nonneg]
  · have h_cont : ContinuousOn (fun T => ∫ t in (0 : ℝ)..T, f t) (Set.Icc 0 1) := by
      intro T hT; apply_rules [intervalIntegral.continuousWithinAt_primitive]; aesop
      simpa using hbdd.1 1 zero_le_one
    have := h_cont 0 (by norm_num); aesop
  · intro x hx; apply_rules [intervalIntegral.integral_hasDerivAt_right]
    · exact hbdd.1 x hx.out.le
    · exact ⟨Set.Ioi 0, Ioi_mem_nhds hx,
        huc.continuousOn.aestronglyMeasurable measurableSet_Ici |> fun h =>
          h.mono_set <| Set.Ioi_subset_Ici_self⟩
    · exact huc.continuousOn.continuousAt <| Ici_mem_nhds hx
  · exact fun x hx => hnn x hx.out.le
