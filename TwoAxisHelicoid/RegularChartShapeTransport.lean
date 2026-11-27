import TwoAxisHelicoid.OriginalRegularChartNormals
import TwoAxisHelicoid.IsothermalComplexAtlas

namespace TwoAxisHelicoid
open Complex Filter Set Topology
open scoped Topology ContDiff

private theorem normalize_positive_multiple (a : ℝ) (c : SurfaceEuclideanSpace) (p : 0<a) :
    ‖a • c‖⁻¹ • (a • c)=‖c‖⁻¹ • c := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos p,mul_inv_rev,smul_smul,mul_assoc,inv_mul_cancel₀ p.ne',mul_one]

private theorem normalize_signed_multiple (a : ℝ) (c : SurfaceEuclideanSpace) (nz : a≠0) :
    ‖a • c‖⁻¹ • (a • c)=‖c‖⁻¹ • c ∨ ‖a • c‖⁻¹ • (a • c)= -(‖c‖⁻¹ • c) := by
  rcases lt_or_gt_of_ne nz with neg|pos
  · right
    have flip : a • c= -((-a) • c) := by simp
    rw [flip,norm_neg,smul_neg,normalize_positive_multiple _ _ (neg_pos.mpr neg)]
  · exact Or.inl (normalize_positive_multiple _ _ pos)

/-- The norm estimate for the actual derivative of the Euclidean unit
normal is unchanged under a regular chart transition of either orientation. -/
theorem chart_normal_derivative_bound_of_change {X Y : ℂ → Fin 3 → ℝ} {k : ℂ → ℂ} {z : ℂ} {B : ℝ}
    (germ : X=ᶠ[𝓝 z] Y ∘ k) (sk : ContDiffAt ℝ 2 k z)
    (rx : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 2 X w ∧ Function.Injective (fderiv ℝ X w))
    (ry : ∀ᶠ w in 𝓝 (k z), ContDiffAt ℝ 2 Y w ∧ Function.Injective (fderiv ℝ Y w))
    (bound : ∀ v, ‖fderiv ℝ (euclideanUnitChartNormal Y) (k z) v‖≤
      B*‖coordinateToEuclidean (fderiv ℝ Y (k z) v)‖) (v : ℂ) :
    ‖fderiv ℝ (euclideanUnitChartNormal X) z v‖≤B*‖coordinateToEuclidean (fderiv ℝ X z v)‖ := by
  let m := euclideanUnitChartNormal Y ∘ k
  let n := euclideanUnitChartNormal X
  have rX := rx.self_of_nhds
  have rY := ry.self_of_nhds
  have dm := (euclideanUnitChartNormal_contDiffAt rY.1 rY.2).differentiableAt one_ne_zero
  have dk := sk.differentiableAt two_ne_zero
  have diff := dm.hasFDerivAt.comp z dk.hasFDerivAt
  have nonzero : m z≠0 := by
    intro h
    have one : ‖m z‖=1 := euclideanUnitChartNormal_unit rY.2
    simp [h] at one
  have choice : ∀ᶠ w in 𝓝 z, n w=m w ∨ n w= -m w := by
    filter_upwards [eventually_eventually_nhds.mpr germ,rx,sk.continuousAt.tendsto.eventually ry,
      sk.eventually (by norm_num)] with w equal hx hy hk
    have cross := surfaceTangentCross_coordinate_change equal (hy.1.differentiableAt two_ne_zero) (hk.differentiableAt two_ne_zero)
    have nz : planeRealJacobian (fderiv ℝ k w)≠0 := by
      intro e
      rw [e,zero_smul] at cross
      exact surfaceTangentCross_ne_zero_of_injective hx.2 cross
    change (‖coordinateToEuclidean (surfaceTangentCross X w)‖⁻¹ • coordinateToEuclidean (surfaceTangentCross X w)=_ ∨
      ‖coordinateToEuclidean (surfaceTangentCross X w)‖⁻¹ • coordinateToEuclidean (surfaceTangentCross X w)=_)
    rw [cross,map_smul]
    exact normalize_signed_multiple _ _ nz
  have sn := (euclideanUnitChartNormal_contDiffAt rX.1 rX.2).continuousAt
  have eqnorm : ‖fderiv ℝ n z v‖=‖fderiv ℝ (euclideanUnitChartNormal Y) (k z) (fderiv ℝ k z v)‖ := by
    rcases continuous_sign_choice_germ sn diff.continuousAt nonzero choice with pos|neg
    · rw [pos.fderiv_eq,diff.fderiv]
      rfl
    · rw [neg.fderiv_eq]
      change ‖fderiv ℝ (-(euclideanUnitChartNormal Y ∘ k)) z v‖=_
      rw [diff.neg.fderiv]
      exact norm_neg _
  rw [show ‖fderiv ℝ (euclideanUnitChartNormal X) z v‖= _ from eqnorm,germ.fderiv_eq,
    fderiv_comp z (rY.1.differentiableAt two_ne_zero) dk]
  exact bound _

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.chart_normal_derivative_bound_of_change
