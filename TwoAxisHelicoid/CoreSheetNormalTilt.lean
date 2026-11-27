import TwoAxisHelicoid.TransverseCoreTubeSheets
import TwoAxisHelicoid.NormalGraphDerivativeConvergence

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology ContDiff RealInnerProductSpace

/-- A quantitative slope estimate for a normal graph, obtained from
the two physical tangent planes. The normal of the moving sheet is
needed only at the point under consideration. -/
theorem core_sheet_height_slope {X N Z : ℂ → SurfaceEuclideanSpace} {u : ℂ → ℝ} {z : ℂ}
    (x : DifferentiableAt ℝ X z) (n : DifferentiableAt ℝ N z) (h : DifferentiableAt ℝ u z)
    (graph : Z =ᶠ[𝓝 z] fun w => X w+u w • N w)
    (unit : ‖N z‖=1) (refPerp : ∀ v, ⟪N z,fderiv ℝ X z v⟫=0)
    {m : SurfaceEuclideanSpace} (movingUnit : ‖m‖=1) (perp : ∀ v, ⟪m,fderiv ℝ Z z v⟫=0)
    (near : ‖m-N z‖≤1/2) :
    ‖fderiv ℝ u z‖ ≤ 2*(‖m-N z‖*‖fderiv ℝ X z‖ + |u z| * ‖fderiv ℝ N z‖) := by
  have one : ⟪N z,N z⟫=1 := by rw [real_inner_self_eq_norm_sq,unit,one_pow]
  have close := abs_real_inner_le_norm (m-N z) (N z)
  rw [inner_sub_left,one,unit,mul_one] at close
  have angle : 1/2≤⟪m,N z⟫ := by linarith [(abs_le.mp (close.trans near)).1]
  have d := ((x.hasFDerivAt.add (h.hasFDerivAt.smul n.hasFDerivAt)).congr_of_eventuallyEq graph).fderiv
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  let a := fderiv ℝ X z v
  let b := fderiv ℝ N z v
  let e := fderiv ℝ u z v
  have sum : ⟪m,a⟫+u z*⟪m,b⟫+e*⟪m,N z⟫=0 := by
    have hv := perp v
    rw [d] at hv
    simpa only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,
      inner_add_right,real_inner_smul_right,add_assoc,a,b,e] using hv
  have proj : ⟪m-N z,a⟫=⟪m,a⟫ := by rw [inner_sub_left,refPerp,sub_zero]
  have base := abs_real_inner_le_norm (m-N z) a
  rw [proj] at base
  have variation := abs_real_inner_le_norm m b
  rw [movingUnit,one_mul] at variation
  have eq : e*⟪m,N z⟫ = -(⟪m,a⟫+u z*⟪m,b⟫) := by linarith
  have bound : |e| * ⟪m,N z⟫ ≤ ‖m-N z‖*‖a‖ + |u z| * ‖b‖ := by
    calc
      |e| * ⟪m,N z⟫ = |e*⟪m,N z⟫| := by rw [abs_mul,abs_of_nonneg (by linarith : 0≤⟪m,N z⟫)]
      _ = |⟪m,a⟫+u z*⟪m,b⟫| := by rw [eq,abs_neg]
      _ ≤ |⟪m,a⟫| + |u z| * |⟪m,b⟫| := by rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ _ := add_le_add base (mul_le_mul_of_nonneg_left variation (abs_nonneg _))
  have bound' := bound.trans (add_le_add
    (mul_le_mul_of_nonneg_left ((fderiv ℝ X z).le_opNorm v) (norm_nonneg _))
    (mul_le_mul_of_nonneg_left ((fderiv ℝ N z).le_opNorm v) (abs_nonneg _)))
  change |e| ≤ _
  have lower := mul_le_mul_of_nonneg_left angle (abs_nonneg e)
  nlinarith only [lower,bound']

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.core_sheet_height_slope
