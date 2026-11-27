import TwoAxisHelicoid.HarmonicComplexCoefficient
import TwoAxisHelicoid.CoordinateMeanCurvature
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

namespace TwoAxisHelicoid
open Complex Matrix Filter InnerProductSpace Laplacian
open scoped Topology
set_option maxHeartbeats 1000000

/-- Differentiate an actual first coordinate derivative along a straight
parameter line. No harmonicity is assumed. -/
theorem coordinate_tangent_line_hasDerivAt {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hX : ContDiffAt ℝ 2 X z) (v w : ℂ) :
    HasDerivAt (fun t : ℝ => fderiv ℝ X (z+t • w) v)
      (fderiv ℝ (fderiv ℝ X) z w v) 0 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ X) z :=
    (hX.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hl : HasDerivAt (fun t : ℝ => z+t • w) w 0 := by
    simpa only [Pi.add_apply,zero_add,one_smul] using!
      (hasDerivAt_const (0 : ℝ) z).add ((hasDerivAt_id 0).smul_const w)
  have hd' : HasFDerivAt (fderiv ℝ X) (fderiv ℝ (fderiv ℝ X) z) (z+(0 : ℝ) • w) := by
    simpa using hd.hasFDerivAt
  have hh := (hd'.comp_hasDerivAt 0 hl).clm_apply (hasDerivAt_const (0 : ℝ) v)
  simpa only [Function.comp_def,ContinuousLinearMap.map_zero,add_zero] using hh

theorem real_vector_dot_hasDerivAt {ι : Type*} [Fintype ι]
    {f g : ℝ → ι → ℝ} {f' g' : ι → ℝ} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => f s ⬝ᵥ g s) (f' ⬝ᵥ g t+f t ⬝ᵥ g') t := by
  simpa only [dotProduct,Finset.sum_add_distrib,Pi.mul_apply] using!
    HasDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => (hasDerivAt_pi.mp hf i).mul (hasDerivAt_pi.mp hg i))

/-- Differentiating the two conformality identities shows that the
coordinate Laplacian is perpendicular to both actual tangent vectors. -/
theorem conformal_coordinate_laplacian_tangent_orthogonal
    {X : ℂ → Fin 3 → ℝ} {z : ℂ} (hX : ContDiffAt ℝ 2 X z)
    (hc : ∀ᶠ w in 𝓝 z,
      fderiv ℝ X w 1 ⬝ᵥ fderiv ℝ X w 1 = fderiv ℝ X w I ⬝ᵥ fderiv ℝ X w I ∧
      fderiv ℝ X w 1 ⬝ᵥ fderiv ℝ X w I = 0) :
    (Δ X z) ⬝ᵥ fderiv ℝ X z 1 = 0 ∧ (Δ X z) ⬝ᵥ fderiv ℝ X z I = 0 := by
  let A := fderiv ℝ X z 1
  let B := fderiv ℝ X z I
  let Q := fderiv ℝ (fderiv ℝ X) z
  have hsym : Q I 1 = Q 1 I :=
    (hX.isSymmSndFDerivAt (by simp)).eq I 1
  have he (v : ℂ) :
      Q v 1 ⬝ᵥ A+A ⬝ᵥ Q v 1 = Q v I ⬝ᵥ B+B ⬝ᵥ Q v I := by
    have hline : Tendsto (fun t : ℝ => z+t • v) (𝓝 0) (𝓝 z) := by
      have hh : Continuous (fun t : ℝ => z+t • v) := by fun_prop
      simpa only [ContinuousAt,zero_smul,add_zero] using hh.continuousAt (x := 0)
    have h := (real_vector_dot_hasDerivAt
      (coordinate_tangent_line_hasDerivAt hX 1 v)
      (coordinate_tangent_line_hasDerivAt hX 1 v)).unique
      ((real_vector_dot_hasDerivAt
        (coordinate_tangent_line_hasDerivAt hX I v)
        (coordinate_tangent_line_hasDerivAt hX I v)).congr_of_eventuallyEq
          (by filter_upwards [hline.eventually hc] with t ht; exact ht.1))
    simpa only [zero_smul,add_zero] using h
  have ho (v : ℂ) : Q v 1 ⬝ᵥ B+A ⬝ᵥ Q v I = 0 := by
    have hline : Tendsto (fun t : ℝ => z+t • v) (𝓝 0) (𝓝 z) := by
      have hh : Continuous (fun t : ℝ => z+t • v) := by fun_prop
      simpa only [ContinuousAt,zero_smul,add_zero] using hh.continuousAt (x := 0)
    have h := (real_vector_dot_hasDerivAt
      (coordinate_tangent_line_hasDerivAt hX 1 v)
      (coordinate_tangent_line_hasDerivAt hX I v)).unique
      ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
        (by filter_upwards [hline.eventually hc] with t ht; exact ht.2))
    simpa only [zero_smul,add_zero] using h
  have he1 := he 1
  have heI := he I
  have ho1 := ho 1
  have hoI := ho I
  rw [hsym] at heI hoI
  rw [dotProduct_comm A (Q 1 1),dotProduct_comm B (Q 1 I)] at he1
  rw [dotProduct_comm A (Q 1 I),dotProduct_comm B (Q I I)] at heI
  rw [dotProduct_comm A (Q 1 I)] at ho1
  rw [dotProduct_comm A (Q I I)] at hoI
  simp only [laplacian_eq_iteratedFDeriv_complexPlane,iteratedFDeriv_two_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,add_dotProduct]
  change Q 1 1 ⬝ᵥ A+Q I I ⬝ᵥ A = 0 ∧ Q 1 1 ⬝ᵥ B+Q I I ⬝ᵥ B = 0
  constructor <;> linarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.conformal_coordinate_laplacian_tangent_orthogonal
