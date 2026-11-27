import TwoAxisHelicoid.DiskBoundarySpinHomotopy
import TwoAxisHelicoid.SpatialGramFrames

namespace TwoAxisHelicoid
open Complex Set Filter Metric
open scoped Matrix

noncomputable def spinDiskBoundary (t : unitInterval) : ℂ := Circle.exp (2*Real.pi*t.1)

theorem spinDiskBoundary_continuous : Continuous spinDiskBoundary :=
  continuous_subtype_val.comp (Circle.exp.continuous.comp (continuous_const.mul continuous_subtype_val))

theorem spinDiskBoundary_norm (t : unitInterval) : ‖spinDiskBoundary t‖ = 1 := Circle.norm_coe _

theorem spinDiskBoundary_ne_zero (t : unitInterval) : spinDiskBoundary t ≠ 0 := Circle.coe_ne_zero _

theorem spinDiskBoundary_endpoints : spinDiskBoundary 1 = spinDiskBoundary 0 := by
  simp [spinDiskBoundary]

theorem spinDiskBoundary_half (t : unitInterval) :
    spinDiskBoundary (secondHalfParameter t) = -spinDiskBoundary (firstHalfParameter t) := by
  have hπ : Circle.exp Real.pi = -1 := Circle.ext (by simp [Circle.coe_exp,Complex.exp_pi_mul_I])
  change ((Circle.exp (2*Real.pi*(t.1/2+1/2)) : Circle) : ℂ) = -((Circle.exp (2*Real.pi*(t.1/2)) : Circle) : ℂ)
  rw [show 2*Real.pi*(t.1/2+1/2) = 2*Real.pi*(t.1/2)+Real.pi by ring,Circle.exp_add,hπ]
  simp

theorem rotateTangentPair_neg_one_val (p : OrthonormalTangentPair) :
    (rotateTangentPair (-1) p).1 = (-p.1.1,-p.1.2) := by
  simp [rotateTangentPair]

/-- The ambient spin along the tangent-adapted boundary of every regular
immersed disk is antiperiodic. Radial contraction keeps the actual
angular directions, whose two vectors both reverse at the center. -/
theorem immersed_disk_boundary_spin_not_closed {F : ℂ → Fin 3 → ℝ}
    (hD : ContinuousOn (fderiv ℝ F) (closedBall 0 1))
    (hi : ∀ z ∈ closedBall (0:ℂ) 1, Function.Injective (fderiv ℝ F z))
    (q : C(unitInterval,UnitQuaternion))
    (hq : ∀ t, (unitQuaternionFrame (q t)).1 =
      spatialGramFrame (fderiv ℝ F (spinDiskBoundary t) (I*spinDiskBoundary t))
        (fderiv ℝ F (spinDiskBoundary t) (I*(I*spinDiskBoundary t)))) : q 1 ≠ q 0 := by
  let z := fun p : unitInterval × unitInterval => (1-p.1.1) • spinDiskBoundary p.2
  have hz : Continuous z := (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
    (spinDiskBoundary_continuous.comp continuous_snd)
  have hzU (p) : z p ∈ closedBall (0:ℂ) 1 := by
    rw [mem_closedBall,dist_zero_right]
    simp only [z,norm_smul,spinDiskBoundary_norm,mul_one,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr p.1.2.2)]
    linarith [p.1.2.1]
  let D := fun p => fderiv ℝ F (z p)
  let v := fun p : unitInterval × unitInterval => I*spinDiskBoundary p.2
  have hcD : Continuous D := hD.comp_continuous hz hzU
  have hcv : Continuous v := continuous_const.mul (spinDiskBoundary_continuous.comp continuous_snd)
  have hnv (p) : v p ≠ 0 := mul_ne_zero I_ne_zero (spinDiskBoundary_ne_zero p.2)
  let H : C(unitInterval × unitInterval,OrthonormalTangentPair) :=
    ⟨fun p => spatialDifferentialFrame (hi _ (hzU p)) (hnv p),
      spatialDifferentialFrame_continuous hcD hcv (fun p => hi _ (hzU p)) hnv⟩
  apply quaternion_homotopic_reversed_frame_not_closed H _ _ q
  · intro t
    apply Subtype.ext
    simpa [H,D,z,v,spatialDifferentialFrame] using hq t
  · intro s
    apply Subtype.ext
    simp only [H,ContinuousMap.coe_mk,spatialDifferentialFrame,z,v,spinDiskBoundary_endpoints]
  · intro t
    apply Subtype.ext
    rw [rotateTangentPair_neg_one_val]
    change spatialGramFrame _ _ = (-_, -_)
    simp only [H,ContinuousMap.coe_mk,spatialDifferentialFrame,z,v,Set.Icc.coe_one,sub_self,zero_smul,
      spinDiskBoundary_half,mul_neg,map_neg,spatialGramFrame_neg]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.immersed_disk_boundary_spin_not_closed
