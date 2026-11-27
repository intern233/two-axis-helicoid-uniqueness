import TwoAxisHelicoid.MinimalGraphClosedForm
import TwoAxisHelicoid.ConformalCoordinateLaplacian

namespace TwoAxisHelicoid
open Complex Set Filter Matrix
open scoped Topology ContDiff
set_option maxHeartbeats 1000000

noncomputable def euclideanGraph (u : ℂ → ℝ) (z : ℂ) : Fin 3 → ℝ := ![z.re,z.im,u z]

theorem euclideanGraph_contDiffAt {u : ℂ → ℝ} {z : ℂ} {n : ℕ∞ω}
    (hu : ContDiffAt ℝ n u z) : ContDiffAt ℝ n (euclideanGraph u) z := by
  apply contDiffAt_pi.mpr
  intro j
  fin_cases j
  · exact reCLM.contDiff.contDiffAt
  · exact imCLM.contDiff.contDiffAt
  · exact hu

theorem euclideanGraph_fderiv {u : ℂ → ℝ} {z : ℂ} (hu : DifferentiableAt ℝ u z) (v : ℂ) :
    fderiv ℝ (euclideanGraph u) z v = ![v.re,v.im,fderiv ℝ u z v] := by
  let D : Fin 3 → ℂ →L[ℝ] ℝ := ![reCLM,imCLM,fderiv ℝ u z]
  have hD : HasFDerivAt (euclideanGraph u) (ContinuousLinearMap.pi D) z := by
    apply hasFDerivAt_pi.mpr
    intro j
    fin_cases j
    · exact reCLM.hasFDerivAt
    · exact imCLM.hasFDerivAt
    · exact hu.hasFDerivAt
  rw [hD.fderiv]
  funext j
  fin_cases j <;> rfl

theorem euclideanGraph_second_derivative {u : ℂ → ℝ} {z : ℂ} (hu : ContDiffAt ℝ 2 u z) (v w : ℂ) :
    fderiv ℝ (fderiv ℝ (euclideanGraph u)) z v w =
      ![0,0,fderiv ℝ (graphSlope u w) z v] := by
  have hh := coordinate_tangent_line_hasDerivAt (euclideanGraph_contDiffAt hu) w v
  have hs := graph_line_deriv ((graphSlope_smooth hu w).differentiableAt one_ne_zero) v
  have hvec : HasDerivAt (fun t : ℝ => ![w.re,w.im,graphSlope u w (z+t • v)] : ℝ → Fin 3 → ℝ)
      ![0,0,fderiv ℝ (graphSlope u w) z v] 0 := by
    apply hasDerivAt_pi.mpr
    intro j
    fin_cases j
    · exact hasDerivAt_const _ _
    · exact hasDerivAt_const _ _
    · exact hs
  apply hh.unique (hvec.congr_of_eventuallyEq ?_)
  have ht : Tendsto (fun t : ℝ => z+t • v) (𝓝 0) (𝓝 z) := by
    have hc : Continuous (fun t : ℝ => z+t • v) := by fun_prop
    simpa only [ContinuousAt,zero_smul,add_zero] using hc.continuousAt (x := 0)
  filter_upwards [ht.eventually (hu.eventually (by norm_num))] with t h
  exact euclideanGraph_fderiv (h.differentiableAt two_ne_zero) w

theorem euclideanGraph_zero_mean_curvature_iff {u : ℂ → ℝ} {z : ℂ} (hu : ContDiffAt ℝ 2 u z) :
    coordinateMeanCurvature (euclideanGraph u) z = 0 ↔ MinimalGraphEquation u z := by
  let p := graphSlope u 1
  let q := graphSlope u I
  let W := graphAreaWeight (p z) (q z)
  have hW : W ≠ 0 := (graphAreaWeight_pos _ _).ne'
  have hD := hu.differentiableAt two_ne_zero
  have hn : unitCrossNormal ![1,0,p z] ![0,1,q z] = W⁻¹ • ![-p z,-q z,1] := by
    have he : (![1,0,p z] : Fin 3 → ℝ) ⨯₃ ![0,1,q z] = ![-p z,-q z,1] := by
      ext j; fin_cases j <;> simp [crossProduct]
    unfold unitCrossNormal
    rw [he]
    have hsq : (![-p z,-q z,1] : Fin 3 → ℝ) ⬝ᵥ ![-p z,-q z,1] = 1+(p z)^2+(q z)^2 := by
      simp [dotProduct,Fin.sum_univ_succ]; ring
    rw [hsq]
    rfl
  unfold coordinateMeanCurvature MinimalGraphEquation
  dsimp only
  rw [euclideanGraph_fderiv hD,euclideanGraph_fderiv hD]
  simp only [one_re,one_im,I_re,I_im,iteratedFDeriv_two_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
  change _ ↔ (1+(q z)^2)*fderiv ℝ p z 1-2*p z*q z*fderiv ℝ q z 1+(1+(p z)^2)*fderiv ℝ q z I = 0
  rw [euclideanGraph_second_derivative hu,euclideanGraph_second_derivative hu,euclideanGraph_second_derivative hu]
  rw [show fderiv ℝ u z 1 = p z from rfl,show fderiv ℝ u z I = q z from rfl,hn]
  simp only [dotProduct_smul,smul_eq_mul]
  simp [dotProduct,Fin.sum_univ_succ]
  field_simp
  ring_nf
  simp only [show 1+(q z)^2+(p z)^2 ≠ 0 from by positivity,or_false,p,q]
  ring_nf

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.euclideanGraph_zero_mean_curvature_iff
