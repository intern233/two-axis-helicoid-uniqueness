import TwoAxisHelicoid.AlignedEndDoublePoles
import TwoAxisHelicoid.FiniteGaussSphericalEstimate
import TwoAxisHelicoid.MeasuredDoublePolePrimitives
import TwoAxisHelicoid.LocalFiniteGaussDevelopment

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped ContDiff

private theorem finite_normal_differentiable (g : ℂ) :
    DifferentiableAt ℝ (coordinateToEuclidean ∘ finiteGaussNormal) g := by
  apply coordinateToEuclidean.differentiableAt.comp
  apply differentiableAt_pi.mpr
  intro j
  have den : 1+normSq g≠0 := ne_of_gt (by linarith [Complex.normSq_nonneg g])
  have ns : DifferentiableAt ℝ normSq g := by
    change DifferentiableAt ℝ (fun w : ℂ => w.re*w.re+w.im*w.im) g
    fun_prop
  have dd : DifferentiableAt ℝ (fun w : ℂ => 1+normSq w) g := (differentiableAt_const (1:ℝ)).add ns
  fin_cases j
  · change DifferentiableAt ℝ (fun w : ℂ => 2*w.re/(1+normSq w)) g
    simp only [div_eq_mul_inv]
    exact ((differentiableAt_const (2:ℝ)).mul reCLM.differentiableAt).mul (dd.inv den)
  · change DifferentiableAt ℝ (fun w : ℂ => 2*w.im/(1+normSq w)) g
    simp only [div_eq_mul_inv]
    exact ((differentiableAt_const (2:ℝ)).mul imCLM.differentiableAt).mul (dd.inv den)
  · change DifferentiableAt ℝ (fun w : ℂ => (normSq w-1)/(1+normSq w)) g
    simp only [div_eq_mul_inv]
    exact (ns.sub_const 1).mul (dd.inv den)

/-- A bound on the ratio of the logarithmic Gauss differential to the height
differential bounds the physical derivative of the unit normal. The estimate
holds throughout the finite nonzero Gauss chart, even when |g| is large. -/
theorem logarithmic_gauss_controls_physical_shape {X : ℂ → Fin 3 → ℝ} {z : ℂ} {k : ℝ}
    (reg : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ X w ∧ ConformalCoordinateDerivatives X w ∧
      immersionComplexCoefficient X w 2≠0)
    (gdiff : DifferentiableAt ℂ (immersionGaussMap X) z)
    (nonneg : 0≤k) (ratio : ‖immersionGaussLogDerivative X z‖ ≤ k*‖immersionComplexCoefficient X z 2‖)
    (v : ℂ) : ‖fderiv ℝ (euclideanUnitChartNormal X) z v‖ ≤
      4*k*‖coordinateToEuclidean (fderiv ℝ X z v)‖ := by
  let p := immersionComplexCoefficient X
  let g := immersionGaussMap X
  let L := nullHorizontalMinus (p z)
  let N := coordinateToEuclidean ∘ finiteGaussNormal
  have loc : euclideanUnitChartNormal X =ᶠ[𝓝 z] N ∘ g := by
    filter_upwards [reg] with w hw
    have hp := immersionComplexCoefficient_null hw.2.1
    have hl := (null_horizontal_nonzero_of_height hp hw.2.2).1
    rw [euclidean_chart_normal_eq_unitCross,(immersionComplexCoefficient_hasFDerivAt hw.1).fderiv]
    apply congrArg (fun a => coordinateToEuclidean a)
    exact (congrArg (fun q => unitCrossNormal (nullRealDerivative q 1) (nullRealDerivative q I))
      (null_in_finite_gauss_chart hp hl)).trans (finiteGaussTriple_oriented_unit_normal _ hl)
  have rc := reg.self_of_nhds
  have hp := immersionComplexCoefficient_null rc.2.1
  have hl : L≠0 := (null_horizontal_nonzero_of_height hp rc.2.2).1
  have gn : g z≠0 := div_ne_zero rc.2.2 hl
  have hh : g z*L=p z 2 := div_mul_cancel₀ _ hl
  have sg : ‖deriv g z‖ ≤ k*‖g z‖^2*‖L‖ := by
    change ‖deriv g z/g z‖≤k*‖p z 2‖ at ratio
    rw [norm_div,←hh,norm_mul] at ratio
    simpa only [pow_two,mul_assoc,mul_left_comm,mul_comm] using (div_le_iff₀ (norm_pos_iff.mpr gn)).mp ratio
  have ds (v : ℂ) : fderiv ℝ g z v=v*deriv g z := by
    exact congrArg (fun T : ℂ →L[ℝ] ℂ => T v) (gdiff.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv
  have bound : ‖fderiv ℝ N (g z) (v*deriv g z)‖≤2*(‖v‖*‖deriv g z‖) := by
    rw [←norm_mul]
    exact ((fderiv ℝ N (g z)).le_opNorm _).trans (mul_le_mul_of_nonneg_right
      (norm_fderiv_le_of_lipschitz ℝ finite_gauss_normal_lipschitz) (norm_nonneg _))
  rw [loc.fderiv_eq,fderiv_comp z (finite_normal_differentiable _) (gdiff.restrictScalars ℝ),
    ContinuousLinearMap.comp_apply,ds,(immersionComplexCoefficient_hasFDerivAt rc.1).fderiv,
    physical_speed_in_finite_gauss_chart hp hl,norm_mul,Complex.normSq_eq_norm_sq]
  apply bound.trans
  change 2*(‖v‖*‖deriv g z‖)≤4*k*((1+‖g z‖^2)/2*(‖L‖*‖v‖))
  nlinarith only [mul_le_mul_of_nonneg_left sg (norm_nonneg v),mul_nonneg (mul_nonneg nonneg (norm_nonneg L)) (norm_nonneg v)]

/-- Equal pole orders imply bounded logarithmic derivative relative to height
on an entire deleted neighborhood, with no sector or winding hypothesis. -/
theorem equal_pole_orders_logarithmic_bound {h g : ℂ → ℂ} {n : ℤ}
    (hm : MeromorphicAt h 0) (gm : MeromorphicAt (logDeriv g) 0)
    (ho : meromorphicOrderAt h 0=n) (go : meromorphicOrderAt (logDeriv g) 0=n) :
    ∃ k : ℝ, 0≤k ∧ ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖logDeriv g z‖≤k*‖h z‖ := by
  let q := fun z => logDeriv g z/h z
  have mq : MeromorphicAt q 0 := gm.div hm
  have non : 0≤meromorphicOrderAt q 0 := by
    change 0≤meromorphicOrderAt (logDeriv g/h) 0
    rw [meromorphicOrderAt_div gm hm,go,ho]
    simp
  obtain ⟨b,lim⟩ := (tendsto_nhds_iff_meromorphicOrderAt_nonneg mq).mpr non
  have hn := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hm).mp (by rw [ho]; simp)
  refine ⟨‖b‖+1,by positivity,?_⟩
  filter_upwards [lim.norm.eventually_lt_const (lt_add_one ‖b‖),hn] with z sm nz
  change ‖logDeriv g z/h z‖<‖b‖+1 at sm
  rw [norm_div] at sm
  exact (div_le_iff₀ (norm_pos_iff.mpr nz)).mp sm.le
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.logarithmic_gauss_controls_physical_shape
#print axioms TwoAxisHelicoid.equal_pole_orders_logarithmic_bound
