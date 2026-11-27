import TwoAxisHelicoid.MinimalChartComplexData
import TwoAxisHelicoid.NullEuclideanMetric
import TwoAxisHelicoid.AnalyticContactAngles
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Conformal
import Mathlib.Analysis.InnerProductSpace.ConformalLinearMap

namespace TwoAxisHelicoid
open Complex Real Function InnerProductGeometry
open scoped ContDiff RealInnerProductSpace ComplexConjugate

/-- The actual Euclidean differential of a regular conformal immersion
preserves every angle in its parameter plane. -/
theorem physical_conformal_differential {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (dx : DifferentiableAt ℝ X z) (null : ConformalCoordinateDerivatives X z)
    (imm : Injective (fderiv ℝ X z)) : IsConformalMap (fderiv ℝ (coordinateToEuclidean ∘ X) z) := by
  let D := fderiv ℝ (coordinateToEuclidean ∘ X) z
  let c := nullMetric (immersionComplexCoefficient X z)
  have write := (coordinateToEuclidean.hasFDerivAt.comp z (immersionComplexCoefficient_hasFDerivAt dx)).fderiv
  have scale (v : ℂ) : ‖D v‖^2=c*‖v‖^2 := by
    dsimp only [D]
    rw [write]
    exact nullRealDerivative_euclidean_norm_sq (immersionComplexCoefficient_null null) v
  have ne : D 1≠0 := by
    have diff := (coordinateToEuclidean.hasFDerivAt.comp z dx.hasFDerivAt).fderiv
    intro eq
    have zero : coordinateToEuclidean (fderiv ℝ X z 1)=0 := by simpa only [D,diff,ContinuousLinearMap.comp_apply] using eq
    have raw := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.injective (zero.trans (map_zero coordinateToEuclidean).symm)
    exact one_ne_zero (imm (raw.trans (map_zero _).symm))
  have pos : 0<c := by
    have s : ‖D 1‖^2=c := by simpa using scale 1
    exact s ▸ sq_pos_of_pos (norm_pos_iff.mpr ne)
  apply (isConformalMap_iff D).mpr
  refine ⟨c,pos,?_⟩
  intro u v
  have s := scale (u+v)
  rw [map_add,norm_add_sq_real,norm_add_sq_real,scale u,scale v] at s
  linarith only [s]

private theorem contact_angle_unit_directions (s t : ℝ) :
    angle (circleMap 0 1 s) (circleMap 0 1 t)=Real.arccos (Real.cos (t-s)) := by
  unfold angle
  rw [real_inner_eq_re_inner ℂ,RCLike.inner_apply]
  change Real.arccos ((circleMap 0 1 t*conj (circleMap 0 1 s)).re /
    (‖circleMap 0 1 s‖*‖circleMap 0 1 t‖))=_
  rw [conj_circleMap_zero,circleMap_zero_mul,circleMap_zero_re]
  simp only [norm_circleMap_zero,abs_one,one_mul,div_one,sub_eq_add_neg]

/-- Consecutive initial tangent directions at a contact of order n
meet at π/n in the Euclidean tangent plane of the actual surface. -/
theorem equal_angle_in_physical_tangent_plane {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (dx : DifferentiableAt ℝ X z) (null : ConformalCoordinateDerivatives X z)
    (imm : Injective (fderiv ℝ X z)) {n : ℕ} (n2 : 2≤n) (C : ℂ) (k : ℤ) :
    let D := fderiv ℝ (coordinateToEuclidean ∘ X) z
    angle (D (circleMap 0 1 (contactArmAngle n C k))) (D (circleMap 0 1 (contactArmAngle n C (k+1))))=Real.pi/n := by
  have step : contactArmAngle n C (k+1)-contactArmAngle n C k=Real.pi/n := by
    simp only [contactArmAngle,Int.cast_add,Int.cast_one]
    ring
  dsimp only
  rw [(physical_conformal_differential dx null imm).preserves_angle,contact_angle_unit_directions,step]
  exact Real.arccos_cos (by positivity) (div_le_self Real.pi_pos.le (by exact_mod_cast (show 1≤n by omega)))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.equal_angle_in_physical_tangent_plane
