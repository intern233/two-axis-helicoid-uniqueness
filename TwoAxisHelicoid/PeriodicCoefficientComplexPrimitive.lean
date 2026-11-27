import TwoAxisHelicoid.RhombicGlobalPrimitiveRegularity
import Mathlib.MeasureTheory.Integral.CircleIntegral

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory
open scoped Topology Interval ComplexConjugate
set_option maxHeartbeats 1200000

private theorem rhombic_sub_constant_periods {t : ℝ} (ht : 0<t) {f : ℂ → ℂ}
    (an : ∀ z∉(rhombicPeriodPair t ht).lattice, AnalyticAt ℂ f z) (c : ℂ) :
    rhombicDownPeriod t (fun z => f z-c)=rhombicDownPeriod t f-(1-I*t)*c ∧
    rhombicUpPeriod t (fun z => f z-c)=rhombicUpPeriod t f-(1+I*t)*c := by
  have integrable (p : ℝ → ℂ) (hp : Continuous p)
      (image : ∀ x∈Icc (-1:ℝ) 1, p x∈complexOpenRect (-2) 0 (-t) t) :
      IntervalIntegrable (fun x => f (p x)) volume (-1) 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    intro x hx
    exact ((an _ (rhombic_open_rectangle_not_mem ht (image _ hx))).continuousAt.comp hp.continuousAt).continuousWithinAt
  have down : Continuous (originalPeriodPath t) := continuous_iff_continuousAt.mpr fun s => (originalPeriodPath_hasDerivAt t s).continuousAt
  have up : Continuous (fun s => conj (originalPeriodPath t s)) := Complex.continuous_conj.comp down
  constructor
  · unfold rhombicDownPeriod
    rw [intervalIntegral.integral_sub (integrable _ down (fun _ => originalPeriodPath_mem_rectangle ht)) intervalIntegrable_const,
      intervalIntegral.integral_const]
    norm_num [Complex.real_smul]
    ring
  · unfold rhombicUpPeriod
    rw [intervalIntegral.integral_sub (integrable _ up (fun _ => conjugatePeriodPath_mem_rectangle ht)) intervalIntegrable_const,
      intervalIntegral.integral_const]
    norm_num [Complex.real_smul]
    ring

/-- Subtracting one complex constant cancels both real generator
periods. Adding back its affine primitive gives a single-valued real
primitive on the entire punctured covering plane. -/
theorem periodic_coefficient_unrestricted_real_primitive {t : ℝ} (ht : 0<t) {f : ℂ → ℂ}
    (an : ∀ z∉(rhombicPeriodPair t ht).lattice, AnalyticAt ℂ f z)
    (per : ∀ z ω, ω∈(rhombicPeriodPair t ht).lattice → f (z+ω)=f z) :
    ∃ U : ℂ → ℝ, ∀ z∉(rhombicPeriodPair t ht).lattice, HasFDerivAt U (realCoefficientDerivative (f z)) z := by
  let b := (rhombicDownPeriod t f).re
  let u := (rhombicUpPeriod t f).re
  let c : ℂ := ⟨(b+u)/2,(b-u)/(2*t)⟩
  let g := fun z => f z-c
  have eq := rhombic_sub_constant_periods ht an c
  have hd : (rhombicDownPeriod t g).re=0 := by
    rw [show rhombicDownPeriod t g=_ from eq.1]
    change (rhombicDownPeriod t f).re-((1-I*t)*c).re=0
    change b-((1-I*t)*c).re=0
    simp [Complex.mul_re,Complex.mul_im,c]
    field_simp
    ring
  have hu : (rhombicUpPeriod t g).re=0 := by
    rw [show rhombicUpPeriod t g=_ from eq.2]
    change u-((1+I*t)*c).re=0
    simp [Complex.mul_re,Complex.mul_im,c]
    field_simp
    ring
  let G := rhombicGlobalRealPrimitive t g
  refine ⟨fun w => G w+(w*c).re,?_⟩
  intro z hz
  have d := rhombicGlobalRealPrimitive_hasFDerivAt ht (fun w hw => (an _ hw).sub analyticAt_const)
    (fun w ω hw => congrArg (fun v => v-c) (per w ω hw)) hd hu hz
  have affine : HasFDerivAt (fun w : ℂ => (w*c).re) (realCoefficientDerivative c) z :=
    (realCoefficientDerivative c).hasFDerivAt
  have e : HasFDerivAt (fun w => G w+(w*c).re) (realCoefficientDerivative (g z)+realCoefficientDerivative c) z := by
    exact d.add affine
  convert e using 1
  ext w
  change (w*f z).re=(w*(f z-c)).re+(w*c).re
  simp only [mul_sub,Complex.sub_re,sub_add_cancel]

/-- Every doubly periodic coefficient holomorphic off a rhombic
lattice has a complex primitive on the complement. Its two complex
generator periods may be arbitrary. In particular isolated essential
singularities at lattice points have zero residue. -/
theorem periodic_coefficient_unrestricted_complex_primitive {t : ℝ} (ht : 0<t) {f : ℂ → ℂ}
    (an : ∀ z∉(rhombicPeriodPair t ht).lattice, AnalyticAt ℂ f z)
    (per : ∀ z ω, ω∈(rhombicPeriodPair t ht).lattice → f (z+ω)=f z) :
    ∃ F : ℂ → ℂ, ∀ z∉(rhombicPeriodPair t ht).lattice, HasDerivAt F (f z) z := by
  obtain ⟨U,du⟩ := periodic_coefficient_unrestricted_real_primitive ht an per
  obtain ⟨V,dv⟩ := periodic_coefficient_unrestricted_real_primitive (f := fun z => -I*f z) ht
    (fun w hw => analyticAt_const.mul (an w hw)) (fun z ω h => congrArg (-I*·) (per z ω h))
  let T : ℝ →L[ℝ] ℂ := I • ofRealCLM
  let F := fun z => ofRealCLM (U z)+T (V z)
  refine ⟨F,?_⟩
  intro z hz
  let J := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) (f z)
  have d := (ofRealCLM.hasFDerivAt.comp z (du z hz)).add (T.hasFDerivAt.comp z (dv z hz))
  have e : J.restrictScalars ℝ=(ofRealCLM.comp (realCoefficientDerivative (f z)))+T.comp (realCoefficientDerivative (-I*f z)) := by
    ext w
    change w*f z=((w*f z).re:ℂ)+I*(((w*(-I*f z)).re:ℝ):ℂ)
    rw [show w*(-I*f z)= -I*(w*f z) by ring]
    simp only [neg_mul,Complex.neg_re,Complex.I_mul_re,neg_neg]
    rw [mul_comm I,Complex.re_add_im]
  simpa only [J,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,one_smul] using!
    (hasFDerivAt_of_restrictScalars ℝ d (f' := J) e).hasDerivAt

/-- The ordinary oriented complex circle integral vanishes for every
circle avoiding the lattice, irrespective of the number of enclosed
lattice points. -/
theorem periodic_coefficient_circle_integral_zero {t : ℝ} (ht : 0<t) {f : ℂ → ℂ}
    (an : ∀ z∉(rhombicPeriodPair t ht).lattice, AnalyticAt ℂ f z)
    (per : ∀ z ω, ω∈(rhombicPeriodPair t ht).lattice → f (z+ω)=f z)
    (a : ℂ) {r : ℝ} (hr : 0<r) (off : Disjoint (Metric.sphere a r) ((rhombicPeriodPair t ht).lattice : Set ℂ)) :
    circleIntegral f a r=0 := by
  obtain ⟨F,d⟩ := periodic_coefficient_unrestricted_complex_primitive ht an per
  let c := circleMap a r
  have reg (θ : ℝ) : c θ∉(rhombicPeriodPair t ht).lattice := Set.disjoint_left.mp off (circleMap_mem_sphere a hr.le θ)
  have cc : Continuous (fun θ => f (c θ)) := continuous_iff_continuousAt.mpr (fun θ => (an _ (reg θ)).continuousAt.comp (continuous_circleMap _ _).continuousAt)
  have deriv (θ : ℝ) : HasDerivAt (F ∘ c) ((circleMap 0 r θ*I)*f (c θ)) θ := (d _ (reg θ)).scomp θ (hasDerivAt_circleMap _ _ θ)
  have hc : IntervalIntegrable (fun θ => (circleMap 0 r θ*I)*f (c θ)) volume 0 (2*Real.pi) :=
    (((continuous_circleMap 0 r).mul continuous_const).mul cc).intervalIntegrable _ _
  have e := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => deriv s) hc
  have close : c (2*Real.pi)=c 0 := by simpa using periodic_circleMap a r 0
  simpa only [circleIntegral,deriv_circleMap,smul_eq_mul,Function.comp_apply,close,sub_self] using e

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.periodic_coefficient_unrestricted_complex_primitive
#print axioms TwoAxisHelicoid.periodic_coefficient_circle_integral_zero
