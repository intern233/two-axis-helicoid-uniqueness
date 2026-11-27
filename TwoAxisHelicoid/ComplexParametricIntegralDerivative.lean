import TwoAxisHelicoid.ComplexParametricIntegral

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory Metric
open scoped Topology

theorem complex_intervalIntegral_hasDerivAt {F : ℂ × ℂ → ℂ} {t : ℂ} {l u : ℝ}
    (hlu : l ≤ u) (hF : ∀ x ∈ Icc l u, ContDiffAt ℂ 1 F (t,(x:ℂ))) :
    HasDerivAt (fun z : ℂ => ∫ x : ℝ in l..u, F (z,(x:ℂ)))
      (∫ x : ℝ in l..u, fderiv ℂ F (t,(x:ℂ)) (1,0)) t := by
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp (complex_integrand_C1_eventually_uniform hF)
  let K : Set (ℂ × ℝ) := closedBall t (r/2) ×ˢ Icc l u
  have hK : IsCompact K := (isCompact_closedBall t (r/2)).prod isCompact_Icc
  have hKr (z : ℂ) (hz : z ∈ closedBall t (r/2)) : z ∈ ball t r :=
    lt_of_le_of_lt hz (half_lt_self hr)
  have hFK (p : ℂ × ℝ) (hp : p ∈ K) : ContDiffAt ℂ 1 F (p.1,(p.2:ℂ)) :=
    hrsub (hKr p.1 hp.1) p.2 hp.2
  let D : ℂ → ℝ → ℂ := fun z x => fderiv ℂ F (z,(x:ℂ)) (1,0)
  have hc : ContinuousOn (fun p : ℂ × ℝ => F (p.1,(p.2:ℂ))) K := by
    intro p hp
    have hm : ContinuousAt (fun q : ℂ × ℝ => (q.1,(q.2:ℂ))) p := by fun_prop
    exact ((hFK p hp).continuousAt.comp (f := fun q : ℂ × ℝ => (q.1,(q.2:ℂ))) hm).continuousWithinAt
  have hcD : ContinuousOn (fun p : ℂ × ℝ => D p.1 p.2) K := by
    intro p hp
    have hm : ContinuousAt (fun q : ℂ × ℝ => (q.1,(q.2:ℂ))) p := by fun_prop
    have hh := ((hFK p hp).continuousAt_fderiv (by norm_num)).clm_apply
      (continuousAt_const : ContinuousAt (fun _ : ℂ × ℂ => ((1,0):ℂ × ℂ)) (p.1,(p.2:ℂ)))
    exact (hh.comp (f := fun q : ℂ × ℝ => (q.1,(q.2:ℂ))) hm).continuousWithinAt
  have hsection (z : ℂ) (hz : z ∈ closedBall t (r/2)) :
      ContinuousOn (fun x : ℝ => F (z,(x:ℂ))) (Icc l u) :=
    hc.comp (f := fun x : ℝ => (z,x)) (by fun_prop) (fun _ hx => ⟨hz,hx⟩)
  have hsectionD (z : ℂ) (hz : z ∈ closedBall t (r/2)) : ContinuousOn (D z) (Icc l u) :=
    hcD.comp (f := fun x : ℝ => (z,x)) (by fun_prop) (fun _ hx => ⟨hz,hx⟩)
  have htK : t ∈ closedBall t (r/2) := mem_closedBall_self (by positivity)
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hcD
  let μ : Measure ℝ := volume.restrict (Icc l u)
  have hmeas : ∀ᶠ z in 𝓝 t, AEStronglyMeasurable (fun x : ℝ => F (z,(x:ℂ))) μ := by
    filter_upwards [ball_mem_nhds t (show 0 < r/2 by positivity)] with z hz
    exact (hsection z (ball_subset_closedBall hz)).aestronglyMeasurable measurableSet_Icc
  have hint : Integrable (fun x : ℝ => F (t,(x:ℂ))) μ :=
    (hsection t htK).integrableOn_compact isCompact_Icc
  have hmeasD : AEStronglyMeasurable (D t) μ :=
    (hsectionD t htK).aestronglyMeasurable measurableSet_Icc
  have hbound : ∀ᵐ x ∂μ, ∀ z ∈ ball t (r/2), ‖D z x‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    intro z hz
    exact hM (z,x) ⟨ball_subset_closedBall hz,hx⟩
  have hdiff : ∀ᵐ (x : ℝ) ∂μ, ∀ z ∈ ball t (r/2), HasDerivAt (fun w : ℂ => F (w,(x:ℂ))) (D z x) z := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    intro z hz
    have hd := ((hFK (z,x) ⟨ball_subset_closedBall hz,hx⟩).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt z ((hasDerivAt_id z).prodMk (hasDerivAt_const z (x:ℂ)))
    exact hd
  have hmInt : Integrable (fun _ : ℝ => M) μ := by
    change IntegrableOn (fun _ : ℝ => M) (Icc l u) volume
    exact integrableOn_const (ne_of_lt isCompact_Icc.measure_lt_top)
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z x => F (z,(x:ℂ))) (F' := D) (bound := fun _ => M) (μ := μ)
    (ball_mem_nhds t (show 0 < r/2 by positivity)) hmeas hint hmeasD hbound hmInt hdiff).2
  have hd' : HasDerivAt (fun z : ℂ => ∫ x : ℝ in l..u, F (z,(x:ℂ))) (∫ x : ℝ in l..u, D t x) t := by
    simpa only [μ,intervalIntegral.integral_of_le hlu,← integral_Icc_eq_integral_Ioc] using hd
  exact hd'


theorem real_intervalIntegral_hasDerivAt_of_complex_C1
    {F : ℂ × ℂ → ℂ} {D : ℝ → ℂ} {t l u : ℝ}
    (hlu : l ≤ u) (hF : ∀ x ∈ Icc l u, ContDiffAt ℂ 1 F ((t:ℂ),(x:ℂ)))
    (hD : ∀ x ∈ Icc l u,
      HasDerivAt (fun r : ℝ => F ((r:ℂ),(x:ℂ))) (D x) t) :
    HasDerivAt (fun r : ℝ => ∫ x : ℝ in l..u, F ((r:ℂ),(x:ℂ)))
      (∫ x : ℝ in l..u, D x) t := by
  have hi := (complex_intervalIntegral_hasDerivAt hlu hF).comp_ofReal
  have he : (∫ x : ℝ in l..u, fderiv ℂ F ((t:ℂ),(x:ℂ)) (1,0)) =
      ∫ x : ℝ in l..u, D x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc l u := by simpa only [uIcc_of_le hlu] using hx
    have hd := ((hF x hx').differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
      (t:ℂ) ((hasDerivAt_id (t:ℂ)).prodMk (hasDerivAt_const (t:ℂ) (x:ℂ)))
    exact hd.comp_ofReal.unique (hD x hx')
  rw [he] at hi
  exact hi

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.real_intervalIntegral_hasDerivAt_of_complex_C1
