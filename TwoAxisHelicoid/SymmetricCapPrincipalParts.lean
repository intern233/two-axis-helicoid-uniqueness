import TwoAxisHelicoid.DoublePoleResidueSymmetry
import TwoAxisHelicoid.GeometricEndFromCapDifferentials

namespace TwoAxisHelicoid
open Complex Set Filter Metric MeasureTheory
open scoped Topology ComplexConjugate ContDiff Manifold

/-- If two double-pole differentials both change sign under the same
pointed holomorphic symmetry, their ratio has a nonzero finite limit.
A conjugate reflection taking the ratio to its negative conjugate makes
that limit imaginary and determines the real pitch. -/
theorem symmetric_double_poles_determine_pitch {h k u v : ℂ → ℂ}
    (mh : MeromorphicAt h 0) (oh : meromorphicOrderAt h 0=(-2:ℤ))
    (mk : MeromorphicAt k 0) (ok : meromorphicOrderAt k 0=(-2:ℤ))
    (an : AnalyticAt ℂ u 0) (u0 : u 0=0) (un : deriv u 0≠0)
    (hp : ∀ᶠ z in 𝓝[≠] (0:ℂ), deriv u z*h (u z)= -h z)
    (kp : ∀ᶠ z in 𝓝[≠] (0:ℂ), deriv u z*k (u z)= -k z)
    (toward : Tendsto v (𝓝[≠] (0:ℂ)) (𝓝[≠] 0))
    (reflects : ∀ᶠ z in 𝓝[≠] (0:ℂ), k (v z)/h (v z)= -conj (k z/h z)) :
    ∃ (α : ℝ) (a : ℂ) (P Q : ℂ → ℂ), α≠0 ∧ a≠0 ∧ AnalyticAt ℂ P 0 ∧ AnalyticAt ℂ Q 0 ∧
      (∀ᶠ z in 𝓝[≠] (0:ℂ), h z=a/z^2+P z) ∧
      ∀ᶠ z in 𝓝[≠] (0:ℂ), k z-I*(α:ℂ)*h z=Q z := by
  obtain ⟨a,P,na,pa,eh⟩ := negated_double_pole_has_zero_residue mh oh an u0 un hp
  obtain ⟨b,S,nb,sa,ek⟩ := negated_double_pole_has_zero_residue mk ok an u0 un kp
  let c := b/a
  have scale (d : ℂ) {f Q : ℂ → ℂ} (aq : AnalyticAt ℂ Q 0)
      (eq : ∀ᶠ z in 𝓝[≠] (0:ℂ), f z=d/z^2+Q z) :
      Tendsto (fun z => z^2*f z) (𝓝[≠] (0:ℂ)) (𝓝 d) := by
    have cc : ContinuousAt (fun z : ℂ => d+z^2*Q z) 0 := continuousAt_const.add ((continuousAt_id.pow 2).mul aq.continuousAt)
    apply (show Tendsto (fun z => d+z^2*Q z) (𝓝[≠] (0:ℂ)) (𝓝 d) by simpa using cc.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [eq,self_mem_nhdsWithin] with z e ne
    change z≠0 at ne
    rw [e]
    field_simp [ne]
  have ratio : Tendsto (fun z => k z/h z) (𝓝[≠] (0:ℂ)) (𝓝 c) := by
    apply ((scale b sa ek).div (scale a pa eh) na).congr'
    filter_upwards [self_mem_nhdsWithin] with z ne
    change z≠0 at ne
    exact mul_div_mul_left _ _ (pow_ne_zero 2 ne)
  have reflected := tendsto_nhds_unique_of_eventuallyEq (ratio.comp toward)
    ((Complex.continuous_conj.continuousAt.tendsto.comp ratio).neg) reflects
  have re : c.re=0 := by
    have atRe := congrArg Complex.re reflected
    simp only [neg_re,conj_re] at atRe
    linarith
  have val : I*(c.im:ℂ)=c := Complex.ext (by simp [re]) (by simp)
  have non : c.im≠0 := fun hz => (div_ne_zero nb na) (by simpa only [hz,ofReal_zero,mul_zero] using val.symm)
  refine ⟨c.im,a,P,fun z => S z-c*P z,non,na,pa,sa.sub (analyticAt_const.mul pa),eh,?_⟩
  filter_upwards [eh,ek] with z h k
  rw [val,h,k]
  have lead : c*a=b := div_mul_cancel₀ _ na
  linear_combination (norm := ring_nf) -(lead)/z^2

/-- A residue-free principal part has vanishing complex height period
on every sufficiently small circle in the original parameter. -/
theorem residue_free_peripheral_height_periods {h P : ℂ → ℂ} {a : ℂ} (pa : AnalyticAt ℂ P 0)
    (eq : ∀ᶠ z in 𝓝[≠] (0:ℂ), h z=a/z^2+P z) :
    ∃ R : ℝ, 0<R ∧ ∀ r∈Ioo (0:ℝ) R, (∮ z in C(0,r), h z)=0 := by
  obtain ⟨R,rp,inside⟩ := Metric.mem_nhdsWithin_iff.mp (eq.and (pa.eventually_analyticAt.filter_mono nhdsWithin_le_nhds))
  have reg (z : ℂ) (hz : z∈ball (0:ℂ) R) : AnalyticAt ℂ P z := by
    by_cases ne : z=0
    · exact ne ▸ pa
    · exact (inside ⟨hz,ne⟩).2
  have diff : DifferentiableOn ℂ P (ball 0 R) := fun z hz => (reg z hz).differentiableAt.differentiableWithinAt
  refine ⟨R,rp,fun r hr => circleIntegral.integral_eq_zero_of_hasDerivWithinAt (f := fun z : ℂ => -a/z+wedgeIntegral 0 z P) hr.1.le ?_⟩
  intro z hz
  have radius : ‖z‖=r := by simpa only [mem_sphere,dist_zero_right] using hz
  have small : z∈ball (0:ℂ) R := by simpa only [mem_ball,dist_zero_right,radius] using hr.2
  have ne : z≠0 := norm_pos_iff.mp (radius ▸ hr.1)
  have polar : HasDerivAt (fun w : ℂ => -a/w) (a/z^2) z := by
    simpa using! (hasDerivAt_const z (-a)).div (hasDerivAt_id z) ne
  rw [(inside ⟨small,ne⟩).1]
  exact (polar.add (diff.isConservativeOn.hasDerivAt_wedgeIntegral diff.continuousOn small)).hasDerivWithinAt

/-- In any genus the two pole orders and the two reflected germ
identities supply the pitch, the peripheral period, and the normalized
geometric exterior in the original physical coordinates. -/
theorem geometric_exterior_of_symmetric_cap_poles {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {X : M → Fin 3 → ℝ}
    (charts : ∀ d∈atlas ℂ M, HarmonicImmersionChart X d) (A : GeometricDoublePoleEnd X)
    (u v : ℂ → ℂ) (an : AnalyticAt ℂ u 0) (u0 : u 0=0) (un : deriv u 0≠0) :
    let Y := X ∘ A.endChart.coord.symm
    let h := fun z => immersionComplexCoefficient Y z 2
    let k := immersionGaussLogDerivative Y
    (∀ᶠ z in 𝓝[≠] (0:ℂ), deriv u z*h (u z)= -h z) →
    (∀ᶠ z in 𝓝[≠] (0:ℂ), deriv u z*k (u z)= -k z) →
    Tendsto v (𝓝[≠] (0:ℂ)) (𝓝[≠] 0) →
    (∀ᶠ z in 𝓝[≠] (0:ℂ), k (v z)/h (v z)= -conj (k z/h z)) →
    ∃ G : GeometricExteriorCoordinate X, G.pitch≠0 ∧ G.correction 0=0 := by
  intro Y h k hp kp toward reflected
  obtain ⟨α,_,_,Q,non,_,pa,qa,eh,ek⟩ := symmetric_double_poles_determine_pitch
    A.height A.heightOrder A.gauss A.gaussOrder an u0 un hp kp toward reflected
  obtain ⟨R,rp,period⟩ := residue_free_peripheral_height_periods pa eh
  obtain ⟨G,eq,zero⟩ := geometric_exterior_of_cap_differentials charts A (α := α) (fun s sp => by
    let r := min R s/2
    have pos : 0<r := half_pos (lt_min rp sp)
    have less := half_lt_self (lt_min rp sp)
    exact ⟨r,⟨pos,less.trans_le (min_le_right _ _)⟩,period r ⟨pos,less.trans_le (min_le_left _ _)⟩⟩) ⟨Q,qa,ek⟩
  exact ⟨G,eq.trans_ne non,zero⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.symmetric_double_poles_determine_pitch
#print axioms TwoAxisHelicoid.geometric_exterior_of_symmetric_cap_poles
