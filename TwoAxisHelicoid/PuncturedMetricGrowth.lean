import TwoAxisHelicoid.PlaneDistortionPowerModulus
import TwoAxisHelicoid.PlaneMetricDirectionalDistortion

namespace TwoAxisHelicoid
open Complex Set Filter Metric
open scoped Topology

theorem centered_plane_chart_punctured_limit (e : OpenPartialHomeomorph ℂ ℂ)
    (src : (0:ℂ)∈e.source) (fix : e 0=0) : Tendsto e (𝓝[≠] (0:ℂ)) (𝓝[≠] 0) := by
  have h := (e.continuousAt src).continuousWithinAt (s := ({0}ᶜ : Set ℂ))
  change Tendsto e (𝓝[≠] (0:ℂ)) (𝓝 (e 0)) at h
  rw [fix] at h
  apply tendsto_nhdsWithin_iff.mpr ⟨h,?_⟩
  filter_upwards [mem_nhdsWithin_of_mem_nhds (e.open_source.mem_nhds src),self_mem_nhdsWithin]
    with z hz nz using fun eq => nz (e.injOn hz src (eq.trans fix.symm))

/-- Polynomial growth of the exterior parameter follows from two-sided
metric bounds near a puncture and a genuine centered change of charts.
The bounds can use different conformal factors at every point. -/
theorem reciprocal_growth_of_punctured_metric (e : OpenPartialHomeomorph ℂ ℂ)
    (src : (0:ℂ)∈e.source) (fix : e 0=0)
    (metric : ∀ᶠ z in 𝓝[≠] (0:ℂ), ContDiffAt ℝ 1 e z ∧
      ∃ m c : ℝ, 0<m ∧ 0<c ∧ ∀ v : ℂ,
        m*‖fderiv ℝ e z v‖^2/4≤c*‖v‖^2 ∧ c*‖v‖^2≤4*(m*‖fderiv ℝ e z v‖^2)) :
    ∃ N : ℕ, 0<N ∧ ∃ C : ℝ, 0<C ∧ ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖(e z)⁻¹‖≤C/‖z‖^N := by
  have tgt : (0:ℂ)∈e.target := fix ▸ e.map_source src
  have sym0 : e.symm 0=0 := (congrArg e.symm fix).symm.trans (e.left_inv src)
  have sT := centered_plane_chart_punctured_limit e.symm tgt sym0
  have inv : ∀ᶠ w in 𝓝[≠] (0:ℂ), ContDiffAt ℝ 1 e.symm w ∧
      ∀ v : ℂ, ‖fderiv ℝ e.symm w v‖^2≤4*|(fderiv ℝ e.symm w).det| *‖v‖^2 := by
    filter_upwards [sT.eventually metric,mem_nhdsWithin_of_mem_nhds (e.open_target.mem_nhds tgt)]
      with w h hw
    obtain ⟨smooth,m,c,hm,hc,bd⟩ := h
    exact inverse_coordinate_distortion e hw smooth hm hc bd
  obtain ⟨r,hr,near⟩ := Metric.mem_nhdsWithin_iff.mp inv
  obtain ⟨s,hs,dom⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds tgt)
  let R := (min r s)/2
  have pos : 0<R := half_pos (lt_min hr hs)
  have small : R<r ∧ R<s := ⟨(half_lt_self (lt_min hr hs)).trans_le (min_le_left _ _),
    (half_lt_self (lt_min hr hs)).trans_le (min_le_right _ _)⟩
  have good (z : ℂ) (nz : 0<‖z‖) (bd : ‖z‖≤R) := near
    (show z∈ball (0:ℂ) r ∩ {0}ᶜ from ⟨by rw [mem_ball,dist_zero_right]; exact bd.trans_lt small.1,norm_pos_iff.mp nz⟩)
  have sd : closedBall (0:ℂ) R⊆e.symm.source := fun z hz => dom
    ((closedBall_subset_ball small.2) hz)
  obtain ⟨N,hN,C,hC,growth⟩ := plane_coordinate_power_modulus e.symm pos (by norm_num : (0:ℝ)<4)
    sd (fun z hn h => (good z hn h).1) (fun z hn h => (good z hn h).2)
  have fT := centered_plane_chart_punctured_limit e src fix
  refine ⟨N,hN,C,hC,?_⟩
  filter_upwards [mem_nhdsWithin_of_mem_nhds (e.open_source.mem_nhds src),self_mem_nhdsWithin,
    fT.eventually self_mem_nhdsWithin, fT.eventually (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) (half_pos pos)))]
    with z hz nz nonzero b
  have size : ‖e z‖<R/2 := by simpa only [mem_ball,dist_zero_right] using b
  have h := growth (e z) (norm_pos_iff.mpr nonzero) size.le
  rw [e.left_inv hz,sym0,sub_zero] at h
  rw [norm_inv,le_div_iff₀ (pow_pos (norm_pos_iff.mpr nz) _)]
  calc
    ‖e z‖⁻¹*‖z‖^N ≤ ‖e z‖⁻¹*(C*‖e z‖) := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (norm_nonneg _))
    _ = C := by field_simp [norm_ne_zero_iff.mpr nonzero]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.reciprocal_growth_of_punctured_metric
