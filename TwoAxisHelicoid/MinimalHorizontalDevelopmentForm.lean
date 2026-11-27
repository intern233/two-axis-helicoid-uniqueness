import TwoAxisHelicoid.FiniteGaussChartMetric
import TwoAxisHelicoid.IsothermalChartOrientation

namespace TwoAxisHelicoid
open Complex Matrix Filter Topology
open scoped Topology

/-- The horizontal complex 1-form evaluated on an ambient tangent vector.
Its imaginary part uses the oriented quarter-turn in the tangent plane. -/
noncomputable def horizontalNullCovector (n : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] ℂ :=
  let C := (crossProduct n).toContinuousLinearMap
  let x := (ContinuousLinearMap.proj 0 : (Fin 3 → ℝ) →L[ℝ] ℝ)
  let y := (ContinuousLinearMap.proj 1 : (Fin 3 → ℝ) →L[ℝ] ℝ)
  Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp ((x-y.comp C).prod (-(x.comp C)-y))

noncomputable def physicalHorizontalForm (X : ℂ → Fin 3 → ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (horizontalNullCovector (unitCrossNormal (fderiv ℝ X z 1) (fderiv ℝ X z I))).comp (fderiv ℝ X z)

private theorem unit_normal_quarter_turn {p : Fin 3 → ℂ} (hp : ComplexNull p) (np : p≠0) (v : ℂ) :
    let D := nullRealDerivative p
    unitCrossNormal (D 1) (D I) ⨯₃ D v=D (I*v) := by
  let D := nullRealDerivative p
  let A := D 1
  let B := D I
  let m := nullMetric p
  obtain ⟨pos,hA,hB,orth⟩ := nullRealDerivative_conformal hp np
  have a : A ⬝ᵥ A=m := by simpa only [dotProduct,← pow_two] using hA
  have b : B ⬝ᵥ B=m := by simpa only [dotProduct,← pow_two] using hB
  have ab : A ⬝ᵥ B=0 := orth
  have ba : B ⬝ᵥ A=0 := (dotProduct_comm _ _).trans ab
  have area : (A ⨯₃ B) ⬝ᵥ (A ⨯₃ B)=m^2 := by rw [cross_dot_cross,a,b,ab,zero_mul,sub_zero,pow_two]
  have form : unitCrossNormal A B=m⁻¹ • (A ⨯₃ B) := by rw [unitCrossNormal,area,Real.sqrt_sq pos.le]
  have rot₁ : unitCrossNormal A B ⨯₃ A=B := by
    rw [form,LinearMap.map_smul_of_tower,LinearMap.smul_apply,cross_cross_eq_smul_sub_smul,a,ba,zero_smul,sub_zero,
      smul_smul,inv_mul_cancel₀ pos.ne',one_smul]
  have rot₂ : unitCrossNormal A B ⨯₃ B= -A := by
    rw [form,LinearMap.map_smul_of_tower,LinearMap.smul_apply,cross_cross_eq_smul_sub_smul,ab,b,zero_smul,zero_sub,
      smul_neg,smul_smul,inv_mul_cancel₀ pos.ne',one_smul]
  change unitCrossNormal A B ⨯₃ D v=D (I*v)
  rw [real_linear_complex_expansion D v,real_linear_complex_expansion D (I*v)]
  change crossProduct (unitCrossNormal A B) (v.re • A+v.im • B)=(I*v).re • A+(I*v).im • B
  simp only [map_add,map_smul,rot₁,rot₂,Complex.mul_re,Complex.mul_im,I_re,I_im,zero_mul,one_mul,zero_sub,add_zero,
    neg_smul,smul_neg,add_comm]

/-- On actual null data the invariant covector is exactly the nonpolar
horizontal Weierstrass coefficient times the complex tangent velocity. -/
theorem horizontalNullCovector_of_null {p : Fin 3 → ℂ} (hp : ComplexNull p) (np : p≠0) (v : ℂ) :
    horizontalNullCovector (unitCrossNormal (nullRealDerivative p 1) (nullRealDerivative p I))
      (nullRealDerivative p v)=v*nullHorizontalMinus p := by
  let D := nullRealDerivative p
  let N := unitCrossNormal (D 1) (D I)
  have quarter : N ⨯₃ D v=D (I*v) := unit_normal_quarter_turn hp np v
  change (⟨D v 0-(N ⨯₃ D v) 1, -(N ⨯₃ D v) 0-D v 1⟩ : ℂ)=v*nullHorizontalMinus p
  rw [quarter]
  apply Complex.ext <;> simp [D,nullHorizontalMinus,Complex.mul_re,Complex.mul_im] <;> ring

/-- A positive local change of real coordinates preserves the oriented
unit normal, so it pulls back the complete horizontal 1-form. -/
theorem physicalHorizontalForm_pullback {X Y : ℂ → Fin 3 → ℝ} {k : ℂ → ℂ} {z : ℂ}
    (same : X =ᶠ[𝓝 z] Y ∘ k) (dy : DifferentiableAt ℝ Y (k z)) (dk : DifferentiableAt ℝ k z)
    (positive : 0<planeRealJacobian (fderiv ℝ k z)) :
    unitCrossNormal (fderiv ℝ X z 1) (fderiv ℝ X z I)=unitCrossNormal (fderiv ℝ Y (k z) 1) (fderiv ℝ Y (k z) I) ∧
    physicalHorizontalForm X z=(physicalHorizontalForm Y (k z)).comp (fderiv ℝ k z) := by
  let d := planeRealJacobian (fderiv ℝ k z)
  have cross := surfaceTangentCross_coordinate_change same dy dk
  have normalized : euclideanUnitChartNormal X z=euclideanUnitChartNormal Y (k z) := by
    unfold euclideanUnitChartNormal
    dsimp only
    rw [cross,map_smul,norm_smul,Real.norm_of_nonneg positive.le,smul_smul,_root_.mul_inv_rev,mul_assoc,
      inv_mul_cancel₀ positive.ne',mul_one]
  have n := surfaceCartesianEquiv.symm.injective ((euclidean_chart_normal_eq_unitCross X z).symm.trans
    (normalized.trans (euclidean_chart_normal_eq_unitCross Y (k z))))
  refine ⟨n,?_⟩
  unfold physicalHorizontalForm
  rw [n,same.fderiv_eq,fderiv_comp z dy dk]
  rfl

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.horizontalNullCovector_of_null
#print axioms TwoAxisHelicoid.physicalHorizontalForm_pullback

