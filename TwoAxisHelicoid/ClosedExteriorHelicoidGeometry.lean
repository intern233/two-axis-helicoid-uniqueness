import TwoAxisHelicoid.AnalyticHelicoidalEndGeometry

namespace TwoAxisHelicoid
open Complex Set Filter Bornology Topology Metric
open scoped Topology

private theorem proper_on_closed_exterior_of_proper_subend {X : ℂ → Fin 3 → ℝ} {r S : ℝ}
    (hc : ContinuousOn X {z : ℂ | r ≤ ‖z‖})
    (hp : IsProperMap (fun z : {w : ℂ // S ≤ ‖w‖} => X z.1)) :
    IsProperMap (fun z : {w : ℂ // r ≤ ‖w‖} => X z.1) := by
  apply proper_restrict_of_bounded_preimages (isClosed_le continuous_const continuous_norm) hc
  intro B _
  let K := (fun z : {w : ℂ // S ≤ ‖w‖} => X z.1) ⁻¹' closedBall 0 B
  have hK : IsCompact K := hp.isCompact_preimage (isCompact_closedBall _ _)
  obtain ⟨D,hD,hbound⟩ := (hK.image continuous_subtype_val).isBounded.exists_pos_norm_le
  refine ⟨max D S,hD.trans_le (le_max_left _ _),?_⟩
  intro z _ hz
  by_cases hs : S ≤ ‖z‖
  · apply (hbound z _).trans (le_max_left _ _)
    exact ⟨⟨z,hs⟩,by simpa [K,mem_closedBall] using hz,rfl⟩
  · exact (le_of_not_ge hs).trans (le_max_right _ _)

private theorem compact_exterior_gaussian_bound {W : ℂ → ℂ} {r S : ℝ}
    (ha : ∀ z : ℂ, r ≤ ‖z‖ → AnalyticAt ℂ W z) :
    ∃ C > (0:ℝ), ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ S → |logGaussGaussianCurvature W z| ≤ C := by
  let K := closedBall (0:ℂ) S ∩ {z : ℂ | r ≤ ‖z‖}
  have compact : IsCompact K := (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm)
  let q := fun z : ℂ => -‖deriv W z‖^2/(Real.cosh (W z).re)^4
  have hq : ContinuousOn q K := by
    intro z hz
    have hol := ha z hz.2
    have num : ContinuousAt (fun w : ℂ => -‖deriv W w‖^2) z := (hol.deriv.continuousAt.norm.pow 2).neg
    have den : ContinuousAt (fun w : ℂ => (Real.cosh (W w).re)^4) z :=
      (Real.continuous_cosh.continuousAt.comp (continuous_re.continuousAt.comp hol.continuousAt)).pow 4
    exact (num.div den (pow_ne_zero _ (Real.cosh_pos _).ne')).continuousWithinAt
  obtain ⟨C,hC,hbound⟩ := (compact.image_of_continuousOn hq).isBounded.exists_pos_norm_le
  refine ⟨C,hC,fun z hz hs => ?_⟩
  rw [logGaussGaussianCurvature_formula (ha z hz).differentiableAt.hasDerivAt]
  exact hbound _ ⟨z,⟨by simpa [mem_closedBall] using hs,hz⟩,rfl⟩

/-- The whole closed exterior is proper and has bounded Gaussian curvature,
including its original boundary circle. Embeddedness only needs a subend. -/
theorem analytic_helicoidal_end_global_geometry {X : ℂ → Fin 3 → ℝ} {f : ℂ → ℂ} {r : ℝ}
    (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0)
    (hfinite : ∀ z : ℂ, r ≤ ‖z‖ → AnalyticAt ℂ (infinityCorrection f) z)
    (hd : ∀ z : ℂ, r ≤ ‖z‖ → HasFDerivAt X (nullRealDerivative
      (weierstrassTriple (exp (I*z+infinityCorrection f z)) 1)) z) :
    IsProperMap (fun z : {w : ℂ // r ≤ ‖w‖} => X z.1) ∧
    (∃ C > (0:ℝ), ∀ z : ℂ, r ≤ ‖z‖ → |logGaussGaussianCurvature (fun w => I*w+infinityCorrection f w) z| ≤ C) ∧
    ∃ S : ℝ, r < S ∧ IsClosedEmbedding (fun z : {w : ℂ // S ≤ ‖w‖} => X z.1) := by
  obtain ⟨S,hS,hp,he,hcurv⟩ := analytic_helicoidal_end_embedded_bounded_curvature
    (X := X) (α := 1) (R₀ := r) hf hf0 (fun z hz => by simpa only [Complex.ofReal_one,mul_one] using hd z hz.le)
  refine ⟨proper_on_closed_exterior_of_proper_subend (fun z hz => (hd z hz).continuousAt.continuousWithinAt) hp,?_,S,hS,he⟩
  let W := fun w : ℂ => I*w+infinityCorrection f w
  have hw (z : ℂ) (hz : r ≤ ‖z‖) : AnalyticAt ℂ W z :=
    (analyticAt_const.mul analyticAt_id).add (hfinite z hz)
  obtain ⟨C,hC,hc⟩ := compact_exterior_gaussian_bound (S := S) hw
  refine ⟨max C 4,hC.trans_le (le_max_left _ _),fun z hz => ?_⟩
  by_cases hs : S ≤ ‖z‖
  · have h := hcurv z hs
    norm_num at h
    exact h.trans (le_max_right _ _)
  · exact (hc z hz (le_of_not_ge hs)).trans (le_max_left _ _)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.analytic_helicoidal_end_global_geometry
