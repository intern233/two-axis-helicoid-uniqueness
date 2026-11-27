import TwoAxisHelicoid.HeightEndConeTails
import TwoAxisHelicoid.ConicalHelicoidTube
import TwoAxisHelicoid.CoordinateTubeHomeomorph

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology
set_option maxHeartbeats 1000000

theorem quarter_rotated_horizontal_cone_coordinates (v : Fin 3 → ℝ) (θ : ℝ)
    (hv : v 2 = θ) :
    coordinateToTube (verticalRotation I v) =
      ((endHorizontalSupport θ v*Real.cos θ-endHorizontalTransverse θ v*Real.sin θ,
        endHorizontalSupport θ v*Real.sin θ+endHorizontalTransverse θ v*Real.cos θ),θ) := by
  apply Prod.ext
  · apply Prod.ext
    · change verticalRotation I v 0 = _
      simp only [verticalRotation_apply,Matrix.cons_val_zero,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub]
      rw [endHorizontalSupport_apply,endHorizontalTransverse_apply]
      nlinarith [congrArg (fun s : ℝ => v 1*s) (Real.sin_sq_add_cos_sq θ)]
    · change verticalRotation I v 1 = _
      simp only [verticalRotation_apply,Matrix.cons_val_one,Matrix.cons_val_zero,Complex.I_re,Complex.I_im,zero_mul,one_mul,add_zero]
      rw [endHorizontalSupport_apply,endHorizontalTransverse_apply]
      nlinarith [congrArg (fun s : ℝ => v 0*s) (Real.sin_sq_add_cos_sq θ)]
  · exact hv

/-- For an actual height-normalized helicoidal end containing the same
vertical axis at both height infinities, the decaying Gauss correction
implies arbitrarily thin normal neighborhoods of the standard helicoid.
This proves the thinness input directly for the axis-bearing case. -/
theorem height_normalized_axis_end_arbitrarily_thin
    {X : ℂ → Fin 3 → ℝ} {F : ℂ → ℂ} (R₀ : ℝ)
    (hX : ∀ z : ℂ, R₀ < ‖z‖ → HasFDerivAt X
      (nullRealDerivative (weierstrassTriple (exp (I*z+F z)) 1)) z)
    (hheight : ∀ z : ℂ, R₀ < ‖z‖ → X z 2 = z.re)
    (hF : Tendsto F (cobounded ℂ) (𝓝 0))
    (haxis : ∃ A : ℝ, ∀ x : ℝ, A < |x| → X (x : ℂ) 0 = 0 ∧ X (x : ℂ) 1 = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ S : ℝ, ∀ z : ℂ, S < ‖z‖ →
      coordinateToTube (verticalRotation I (X z)) ∈ helicoidTubeEquiv.target ∧
      |helicoidSignedDistance (coordinateToTube (verticalRotation I (X z)))| ≤ ε := by
  intro ε hε
  let κ := min ε (1/2)
  have hκ0 : 0 < κ := lt_min hε (by norm_num)
  have hκ : κ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hκeps : κ ≤ ε := min_le_left _ _
  obtain ⟨T,_hT,hTcone⟩ := height_end_axis_arbitrarily_narrow_cones 1 R₀
    (by simpa only [Complex.ofReal_one,mul_one] using hX) hF haxis κ hκ0
  refine ⟨max T R₀,?_⟩
  intro z hz
  have hzt : T < ‖z‖ := (le_max_left _ _).trans_lt hz
  have hzr : R₀ < ‖z‖ := (le_max_right _ _).trans_lt hz
  have hc : |endHorizontalTransverse z.re (X z)| ≤ κ*|endHorizontalSupport z.re (X z)| := by
    simpa only [one_mul] using hTcone z hzt
  rw [quarter_rotated_horizontal_cone_coordinates (X z) z.re (hheight z hzr)]
  have ht := horizontal_cone_in_helicoid_tube (θ := z.re) hκ0.le hκ hc
  exact ⟨ht.1,ht.2.trans hκeps⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.height_normalized_axis_end_arbitrarily_thin
