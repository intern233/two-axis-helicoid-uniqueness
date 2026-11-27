import TwoAxisHelicoid.AwayAxisGraphAngle
import TwoAxisHelicoid.HelicoidRelativeHorizontal
import TwoAxisHelicoid.NullCoordinateRecognition

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology ComplexConjugate

/-- Along a complex parameter direction the two actual horizontal
Weierstrass coordinates have this single complex velocity. -/
theorem weierstrass_horizontal_velocity (g v : ℂ) :
    spatialGraphProjection 0 1 (nullRealDerivative (weierstrassTriple g 1) v)=(conj (v/g)-v*g)/2 := by
  change Complex.mk (v*((g⁻¹-g)/2*1)).re (v*(I*(g⁻¹+g)/2*1)).re=_
  apply Complex.ext
  · simp [div_eq_mul_inv,Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im]
    ring
  · simp [div_eq_mul_inv,Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im]
    ring

theorem normal_graph_horizontal_ray_phase {M : Type*} [TopologicalSpace M] {Y : M → Fin 3 → ℝ}
    (graph : HasHelicoidC1End (coordinateToTube ∘ Y)) (cy : Continuous Y) (p : ℝ → M)
    (grow : Tendsto (fun t => ‖spatialGraphProjection 0 1 (Y (p t))‖) atTop atTop) :
    let Z := fun t => exp (((-(Y (p t) 2):ℝ):ℂ)*I)*spatialGraphProjection 0 1 (Y (p t))
    Tendsto (fun t => Z t/conj (Z t)) atTop (𝓝 1) := by
  let T := coordinateToTube ∘ Y
  let W := fun t => spatialGraphProjection 0 1 (Y (p t))
  have form (t : ℝ) : tubeRelativeHorizontal (T (p t))=exp (((-(Y (p t) 2):ℝ):ℂ)*I)*W t := tubeRelativeHorizontal_exp _
  have normEq (t : ℝ) : ‖tubeRelativeHorizontal (T (p t))‖=‖W t‖ := by rw [form,norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
  have esc : Tendsto (fun t => ‖T (p t)‖) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [grow.eventually_ge_atTop (2*b)] with t big
    have up := norm_le_abs_re_add_abs_im (W t)
    change ‖W t‖≤|Y (p t) 0|+|Y (p t) 1| at up
    have a : |Y (p t) 0|≤‖T (p t)‖ := (le_max_left _ _).trans (le_max_left _ _)
    have d : |Y (p t) 1|≤‖T (p t)‖ := (le_max_right _ _).trans (le_max_left _ _)
    change 2*b≤‖W t‖ at big
    linarith
  have h := graph.relative_phase_on_escaping_ray (coordinateToTube.continuous.comp cy) esc (grow.congr fun t => (normEq t).symm)
  exact h.congr fun t => congrArg (fun w : ℂ => w/conj w) (form t)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.weierstrass_horizontal_velocity
#print axioms TwoAxisHelicoid.normal_graph_horizontal_ray_phase
