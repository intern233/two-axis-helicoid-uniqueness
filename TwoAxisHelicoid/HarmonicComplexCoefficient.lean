import TwoAxisHelicoid.HolomorphicNullImmersion
import TwoAxisHelicoid.RhombicGlobalPrimitiveRegularity
import Mathlib.Analysis.Complex.Harmonic.Analytic

namespace TwoAxisHelicoid
open Complex Set InnerProductSpace

noncomputable def scalarComplexCoefficient (F : ℂ → ℝ) (z : ℂ) : ℂ :=
  (fderiv ℝ F z 1 : ℂ)-I*(fderiv ℝ F z I : ℂ)

noncomputable def immersionComplexCoefficient (X : ℂ → Fin 3 → ℝ) (z : ℂ) : Fin 3 → ℂ :=
  fun j => scalarComplexCoefficient (fun w => X w j) z

theorem realCoefficientDerivative_reconstruct (D : ℂ →L[ℝ] ℝ) :
    realCoefficientDerivative ((D 1 : ℂ)-I*(D I : ℂ)) = D := by
  ext w
  have hw : w.re • (1 : ℂ)+w.im • I = w := by
    apply Complex.ext <;> simp [Complex.real_smul]
  change (w*((D 1 : ℂ)-I*(D I : ℂ))).re = D w
  calc (w*((D 1 : ℂ)-I*(D I : ℂ))).re = w.re*D 1+w.im*D I := by
          simp [Complex.mul_re,Complex.mul_im]
      _ = D (w.re • (1 : ℂ)+w.im • I) := by simp only [map_add,map_smul,smul_eq_mul]
      _ = D w := congrArg D hw

theorem scalarComplexCoefficient_hasFDerivAt {F : ℂ → ℝ} {z : ℂ}
    (hF : DifferentiableAt ℝ F z) : HasFDerivAt F (realCoefficientDerivative (scalarComplexCoefficient F z)) z := by
  rw [scalarComplexCoefficient,realCoefficientDerivative_reconstruct]
  exact hF.hasFDerivAt

theorem scalarComplexCoefficient_analyticAt {F : ℂ → ℝ} {z : ℂ}
    (hF : HarmonicAt F z) : AnalyticAt ℂ (scalarComplexCoefficient F) z :=
  _root_.HarmonicAt.analyticAt_complex_partial hF

theorem immersionComplexCoefficient_hasFDerivAt {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hX : DifferentiableAt ℝ X z) :
    HasFDerivAt X (nullRealDerivative (immersionComplexCoefficient X z)) z := by
  have hj (j : Fin 3) : HasFDerivAt (fun w => X w j)
      (realCoefficientDerivative (immersionComplexCoefficient X z j)) z :=
    scalarComplexCoefficient_hasFDerivAt
      (((ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).differentiableAt).comp z hX)
  convert hasFDerivAt_pi.mpr hj using 1
  ext w j
  rfl

def ConformalCoordinateDerivatives (X : ℂ → Fin 3 → ℝ) (z : ℂ) : Prop :=
  (∑ j : Fin 3, (fderiv ℝ (fun w => X w j) z 1)^2) =
      ∑ j : Fin 3, (fderiv ℝ (fun w => X w j) z I)^2 ∧
    (∑ j : Fin 3, fderiv ℝ (fun w => X w j) z 1*fderiv ℝ (fun w => X w j) z I) = 0

theorem immersionComplexCoefficient_null {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hc : ConformalCoordinateDerivatives X z) : ComplexNull (immersionComplexCoefficient X z) := by
  rcases hc with ⟨heq,horth⟩
  norm_num [Fin.sum_univ_succ] at heq horth
  unfold ComplexNull immersionComplexCoefficient scalarComplexCoefficient
  apply Complex.ext <;>
    simp only [Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,pow_two,
      Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.zero_re,Complex.zero_im,zero_mul,mul_zero,zero_add,
      one_mul,sub_zero,zero_sub] <;> nlinarith

theorem immersionComplexCoefficient_regular {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hX : DifferentiableAt ℝ X z) (hinj : Function.Injective (fderiv ℝ X z)) :
    immersionComplexCoefficient X z ≠ 0 := by
  intro hp
  have he := (immersionComplexCoefficient_hasFDerivAt hX).fderiv
  have h10 : (1 : ℂ) = 0 := by
    apply hinj
    rw [he,hp]
    ext j
    simp
  exact one_ne_zero h10

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.scalarComplexCoefficient_analyticAt
#print axioms TwoAxisHelicoid.immersionComplexCoefficient_null
#print axioms TwoAxisHelicoid.immersionComplexCoefficient_regular
