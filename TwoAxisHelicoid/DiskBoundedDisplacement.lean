import TwoAxisHelicoid.DiskMobiusDistance

namespace TwoAxisHelicoid
open Complex Metric Set Filter
open scoped Topology ComplexConjugate

/-- A uniform pseudohyperbolic displacement bound forces a Euclidean
displacement that tends uniformly to zero on the boundary circle. -/
theorem disk_euclidean_displacement {F : ℂ → ℂ} {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    {z : ℂ} (hz : z ∈ complexUnitDisk) (hf : F z ∈ complexUnitDisk)
    (h : ‖diskMobius z (F z)‖ ≤ r) :
    ‖F z-z‖ ≤ r/(1-r)*(1-‖z‖^2) := by
  have hden := norm_pos_iff.mpr (diskMobius_den_ne hz hf)
  rw [diskMobius,norm_div,div_le_iff₀ hden] at h
  have hz' : ‖z‖ < 1 := by simpa using hz
  have hpos : 0 ≤ 1-‖z‖^2 := by nlinarith [norm_nonneg z]
  have he : 1-conj z*F z = (1-conj z*z)-conj z*(F z-z) := by ring
  have hnorm : ‖1-conj z*z‖ = 1-‖z‖^2 := by
    rw [mul_comm (conj z) z,Complex.mul_conj,← Complex.ofReal_one,← Complex.ofReal_sub,
      Complex.norm_real,← Complex.sq_norm,Real.norm_of_nonneg hpos]
  have hsub := norm_sub_le (1-conj z*z) (conj z*(F z-z))
  rw [← he,hnorm,norm_mul,norm_conj] at hsub
  have hh := (mul_le_mul_of_nonneg_left hsub hr)
  have ht : r*(‖z‖*‖F z-z‖) ≤ r*‖F z-z‖ :=
    mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg (sub_nonneg.mpr hz'.le) (norm_nonneg (F z-z))]) hr
  rw [div_mul_eq_mul_div,le_div_iff₀ (sub_pos.mpr hr1)]
  nlinarith

/-- A holomorphic self-map of the disk with uniformly bounded hyperbolic
displacement is the identity. Its difference from the identity extends
continuously by zero to the boundary, so the maximum principle applies. -/
theorem disk_identity_of_bounded_displacement {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F complexUnitDisk)
    (hf : MapsTo F complexUnitDisk complexUnitDisk) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hb : ∀ z ∈ complexUnitDisk, ‖diskMobius z (F z)‖ ≤ r) :
    EqOn F id complexUnitDisk := by
  classical
  let U := fun z : ℂ => if z ∈ complexUnitDisk then F z-z else 0
  let C := r/(1-r)
  have hC : 0 ≤ C := div_nonneg hr (sub_nonneg.mpr hr1.le)
  have Uin (z : ℂ) (hz : z ∈ complexUnitDisk) : U z = F z-z := ite_eq_left_iff.mpr (fun h => (h hz).elim)
  have Uout (z : ℂ) (hz : z ∉ complexUnitDisk) : U z = 0 := ite_eq_right_iff.mpr (fun h => (hz h).elim)
  have hin {w : ℂ} (hw : w ∈ complexUnitDisk) : U =ᶠ[𝓝 w] fun z => F z-z := by
    filter_upwards [isOpen_ball.mem_nhds hw] with z hz
    exact Uin z hz
  have ha {w : ℂ} (hw : w ∈ complexUnitDisk) : AnalyticAt ℂ U w :=
    ((hF w hw).sub analyticAt_id).congr (hin hw).symm
  have hnorm (z : ℂ) : ‖U z‖ ≤ C*|1-‖z‖^2| := by
    by_cases hz : z ∈ complexUnitDisk
    · have he := disk_euclidean_displacement hr hr1 hz (hf hz) (hb z hz)
      rw [Uin z hz]
      exact he.trans (mul_le_mul_of_nonneg_left (le_abs_self _) hC)
    · rw [Uout z hz,norm_zero]
      exact mul_nonneg hC (abs_nonneg (1-‖z‖^2))
  have hc : DiffContOnCl ℂ U complexUnitDisk := by
    refine ⟨fun w hw => (ha hw).differentiableAt.differentiableWithinAt,?_⟩
    intro w hw
    by_cases hd : w ∈ complexUnitDisk
    · exact (ha hd).continuousAt.continuousWithinAt
    · have hw' : ‖w‖ = 1 := by
        have hle : ‖w‖ ≤ 1 := by
          have hh : w ∈ closedBall (0:ℂ) 1 := closure_minimal ball_subset_closedBall isClosed_closedBall hw
          simpa only [mem_closedBall,dist_zero_right] using hh
        exact le_antisymm hle (le_of_not_gt (by simpa using hd))
      have hlim : Tendsto (fun z : ℂ => C*|1-‖z‖^2|) (𝓝 w) (𝓝 0) := by
        have hh : Continuous (fun z : ℂ => C*|1-‖z‖^2|) := by fun_prop
        have hzero : C*|1-‖w‖^2| = 0 := by rw [hw']; norm_num
        exact hzero ▸ hh.continuousAt.tendsto
      apply ContinuousAt.continuousWithinAt
      change Tendsto U (𝓝 w) (𝓝 (U w))
      rw [Uout w hd]
      exact squeeze_zero_norm hnorm hlim
  have hz : EqOn U (fun _ => 0) (frontier complexUnitDisk) := fun w hw => by
    have hop : IsOpen complexUnitDisk := isOpen_ball
    rw [hop.frontier_eq] at hw
    exact Uout w hw.2
  have hall := Complex.eqOn_closure_of_eqOn_frontier (isBounded_ball (x := (0:ℂ)) (r := 1)) hc
    (f := U) (g := fun _ => (0:ℂ)) diffContOnCl_const hz
  intro w hw
  have he := hall (subset_closure hw)
  change U w = 0 at he
  exact sub_eq_zero.mp ((Uin w hw).symm.trans he)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.disk_identity_of_bounded_displacement
