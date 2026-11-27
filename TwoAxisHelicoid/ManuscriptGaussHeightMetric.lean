import TwoAxisHelicoid.ManuscriptHorizontalPeriodOpposition
import TwoAxisHelicoid.CoordinateMetricEnd
import TwoAxisHelicoid.FiniteGaussChartMetric

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaGauss thetaA

private theorem null_metric_horizontal_norms {p : Fin 3 → ℂ} (null : ComplexNull p) :
    Real.sqrt (nullMetric p)=(‖nullHorizontalPlus p‖+‖nullHorizontalMinus p‖)/2 := by
  have energy := (complexNull_real_identities null).1
  have first : 4*nullMetric p=‖nullHorizontalPlus p‖^2+‖nullHorizontalMinus p‖^2+2*‖p 2‖^2 := by
    simp only [← Complex.normSq_eq_norm_sq,nullHorizontalPlus,nullHorizontalMinus,
      Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
      Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,
      zero_sub,zero_add]
    unfold nullMetric at energy ⊢
    linear_combination 2*energy
  have prod := congrArg (fun z : ℂ => ‖z‖) (null_horizontal_product null)
  simp only [norm_mul,norm_neg,norm_pow] at prod
  apply (Real.sqrt_eq_iff_eq_sq (by unfold nullMetric; positivity) (by positivity)).mpr
  nlinarith only [first,prod]

/-- Regular expression for the metric at every finite point, including
both translates of the finite Gauss divisor. -/
theorem manuscript_metric_horizontal_norms {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    {z : ℂ} (hz : z∉(rhombicPeriodPair t ht).lattice) :
    Real.sqrt (nullMetric (coordinateData t a c ht z)) =
      (‖manuscriptOmegaPlus t a c z‖+‖manuscriptOmegaMinus t a c z‖)/2 := by
  have identify :
      nullHorizontalPlus (coordinateData t a c ht z) = -manuscriptOmegaPlus t a c z ∧
      nullHorizontalMinus (coordinateData t a c ht z) = manuscriptOmegaMinus t a c z := by
    constructor <;> dsimp [nullHorizontalPlus,nullHorizontalMinus,manuscriptOmegaMinus,manuscriptOmegaPlus,coordinateData] <;>
      ring_nf <;> simp [I_sq] <;> ring
  rw [null_metric_horizontal_norms (coordinateData_null ht ha hz),identify.1,identify.2,norm_neg]

/-- The manuscript's expression for ds evaluated on an arbitrary complex
tangent vector. Its Gauss quotient is finite and nonzero on this domain. -/
theorem manuscript_gauss_height_line_element {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    (hc : c≠0) {z : ℂ} (hz : z∉(rhombicPeriodPair t ht).lattice)
    (hm : z-a∉(rhombicPeriodPair t ht).lattice) (hp : z+a∉(rhombicPeriodPair t ht).lattice) (v : ℂ) :
    ‖coordinateToEuclidean (nullRealDerivative (coordinateData t a c ht z) v)‖ =
      (‖thetaGauss t a 1 z‖+‖(thetaGauss t a 1 z)⁻¹‖)/2*‖coordinateData t a c ht z 2*v‖ := by
  obtain ⟨plus,minus⟩ := manuscript_omega_gauss_height (c:=c) ht ha hz hm hp
  rw [nullRealDerivative_euclidean_norm (coordinateData_null ht ha hz) (coordinateData_ne_zero ht ha hc hz),
    manuscript_metric_horizontal_norms ht ha hz,plus,minus]
  simp only [norm_mul]; ring

/-- The finite Gauss chart has a regular expression through every
translate of +a, with no division by the vanishing height differential. -/
theorem manuscript_metric_finite_gauss_chart {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    {z : ℂ} (hz : z∉(rhombicPeriodPair t ht).lattice)
    (hp : z+a∉(rhombicPeriodPair t ht).lattice) :
    Real.sqrt (nullMetric (coordinateData t a c ht z)) =
      (1+‖thetaGauss t a 1 z‖^2)/2*‖manuscriptOmegaMinus t a c z‖ := by
  have factor : manuscriptOmegaPlus t a c z=(thetaGauss t a 1 z)^2*manuscriptOmegaMinus t a c z := by
    by_cases hm : z-a∈(rhombicPeriodPair t ht).lattice
    · have hsa := (thetaSigma_zero_iff_lattice_of_pos ht ht (z-a)).mpr hm
      have g0 : thetaGauss t a 1 z=0 := by simp [thetaGauss,hsa]
      have a0 := (thetaA_zero_iff_shift_lattice ht
        (real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2])) hz).mpr hm
      simp [manuscriptOmegaPlus,g0,a0]
    · obtain ⟨plus,minus⟩ := manuscript_omega_gauss_height (c:=c) ht ha hz hm hp
      rw [plus,minus]
      field_simp [thetaGauss_ne_zero ht a 1 hm hp]
  rw [manuscript_metric_horizontal_norms ht ha hz,factor,norm_mul,norm_pow]
  ring

/-- The reciprocal chart uses -g(-z), which agrees with 1/g away from
the divisor. It is regular through the translates of -a. -/
theorem manuscript_metric_reciprocal_gauss_chart {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    {z : ℂ} (hz : z∉(rhombicPeriodPair t ht).lattice)
    (hm : z-a∉(rhombicPeriodPair t ht).lattice) :
    Real.sqrt (nullMetric (coordinateData t a c ht z)) =
      (1+‖-thetaGauss t a 1 (-z)‖^2)/2*‖manuscriptOmegaPlus t a c z‖ := by
  have hnz : -z∉(rhombicPeriodPair t ht).lattice := by simpa using hz
  have hnp : -z+a∉(rhombicPeriodPair t ht).lattice := by
    simpa only [show -z+(a:ℂ)= -(z-a) by ring,neg_mem_iff] using hm
  have reflected := manuscript_metric_finite_gauss_chart (c:=c) ht ha hnz hnp
  rw [manuscript_metric_horizontal_norms ht ha hnz] at reflected
  rw [manuscript_metric_horizontal_norms ht ha hz]
  simpa only [manuscriptOmegaMinus,neg_neg,norm_neg,add_comm] using reflected

/-- The exact finite nonzero limiting metric factors at the translates
of the simple Gauss zero and pole, separately. -/
theorem manuscript_metric_at_finite_divisor {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    (hc : c≠0) {z : ℂ} (hz : z∉(rhombicPeriodPair t ht).lattice) :
    (z-a∈(rhombicPeriodPair t ht).lattice →
      manuscriptOmegaPlus t a c z=0 ∧ manuscriptOmegaMinus t a c z≠0 ∧
        Real.sqrt (nullMetric (coordinateData t a c ht z))=‖manuscriptOmegaMinus t a c z‖/2) ∧
    (z+a∈(rhombicPeriodPair t ht).lattice →
      manuscriptOmegaMinus t a c z=0 ∧ manuscriptOmegaPlus t a c z≠0 ∧
        Real.sqrt (nullMetric (coordinateData t a c ht z))=‖manuscriptOmegaPlus t a c z‖/2) := by
  have haL := real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2] : a<2)
  have hnz : -z∉(rhombicPeriodPair t ht).lattice := by simpa using hz
  have pair := thetaA_pair_not_both_zero ht ha hz
  have metric := manuscript_metric_horizontal_norms (c:=c) ht ha hz
  constructor
  · intro h
    have zero := (thetaA_zero_iff_shift_lattice ht haL hz).mpr h
    have positive := pair.resolve_left (fun hn => hn zero)
    have vanish : manuscriptOmegaPlus t a c z=0 := by simp [manuscriptOmegaPlus,zero]
    exact ⟨vanish,neg_ne_zero.mpr (mul_ne_zero (Complex.ofReal_ne_zero.mpr hc) positive),
      by simpa only [vanish,norm_zero,zero_add] using metric⟩
  · intro h
    have hm : -z-a∈(rhombicPeriodPair t ht).lattice := by
      simpa only [show -z-(a:ℂ)= -(z+a) by ring,neg_mem_iff] using h
    have zero := (thetaA_zero_iff_shift_lattice ht haL hnz).mpr hm
    have positive := pair.resolve_right (fun hn => hn zero)
    have vanish : manuscriptOmegaMinus t a c z=0 := by simp [manuscriptOmegaMinus,manuscriptOmegaPlus,zero]
    exact ⟨vanish,mul_ne_zero (Complex.ofReal_ne_zero.mpr hc) positive,
      by simpa only [vanish,norm_zero,add_zero] using metric⟩

theorem manuscript_metric_continuous_at_finite_point {t a c : ℝ} (ht : 0<t)
    {z : ℂ} (hz : z∉(rhombicPeriodPair t ht).lattice) :
    ContinuousAt (fun w => Real.sqrt (nullMetric (coordinateData t a c ht w))) z := by
  have h := (coordinateData_analyticAt (a:=a) (c:=c) ht hz).continuousAt
  have hj (j : Fin 3) : ContinuousAt (fun w => (coordinateData t a c ht w j).re) z :=
    Complex.continuous_re.continuousAt.comp ((continuous_apply j).continuousAt.comp h)
  exact Real.continuous_sqrt.continuousAt.comp (((hj 0).pow 2).add ((hj 1).pow 2) |>.add ((hj 2).pow 2))

/-- The equality and both inequalities of the displayed line element in
§6.3 on the same punctured neighborhood, with C=|c|/2. -/
theorem manuscript_line_element_puncture_chain {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    (hc : c≠0) : ∀ᶠ z : ℂ in 𝓝[≠] 0, ∀ v : ℂ,
    let p := coordinateData t a c ht z
    let ds := ‖coordinateToEuclidean (nullRealDerivative p v)‖
    ds=(‖thetaGauss t a 1 z‖+‖(thetaGauss t a 1 z)⁻¹‖)/2*‖p 2*v‖ ∧
      ‖p 2*v‖≤ds ∧ |c|/2*‖v‖/‖z‖^2≤‖p 2*v‖ := by
  let L := rhombicPeriodPair t ht
  have aoff : (a:ℂ)∉L.lattice := real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2])
  have minusoff : (0:ℂ)-(a:ℂ)∉L.lattice := by simpa using aoff
  have plusoff : (0:ℂ)+(a:ℂ)∉L.lattice := by simpa using aoff
  have hm := (continuousAt_id.sub_const (a:ℂ)).eventually
    (L.isClosed_lattice.isOpen_compl.mem_nhds minusoff)
  have hp := (continuousAt_id.add_const (a:ℂ)).eventually
    (L.isClosed_lattice.isOpen_compl.mem_nhds plusoff)
  have regular : ∀ᶠ z : ℂ in 𝓝[≠] (0:ℂ), z ∉ (L.lattice : Set ℂ) \ {0} :=
    nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0)
  filter_upwards [regular,self_mem_nhdsWithin,hm.filter_mono nhdsWithin_le_nhds,
    hp.filter_mono nhdsWithin_le_nhds,weierstrass_pole_lower_bound ht (a:ℂ)] with z hz hz0 hm hp pole
  have off : z∉L.lattice := fun h => hz ⟨h,hz0⟩
  intro v
  dsimp only
  refine ⟨manuscript_gauss_height_line_element ht ha hc off hm hp v,?_,?_⟩
  · rw [nullRealDerivative_euclidean_norm (coordinateData_null ht ha off) (coordinateData_ne_zero ht ha hc off),norm_mul]
    exact mul_le_mul_of_nonneg_right (sqrt_nullMetric_ge_third_norm (coordinateData_null ht ha off)
      (coordinateData_ne_zero ht ha hc off)) (norm_nonneg _)
  · have bound := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left pole (abs_nonneg c)) (norm_nonneg v)
    change |c|/2*‖v‖/‖z‖^2 ≤ ‖(I*c*(L.weierstrassP z-L.weierstrassP a))*v‖
    simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
    convert bound using 1
    ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.manuscript_gauss_height_line_element
#print axioms TwoAxisHelicoid.manuscript_metric_reciprocal_gauss_chart
#print axioms TwoAxisHelicoid.manuscript_metric_at_finite_divisor
#print axioms TwoAxisHelicoid.manuscript_line_element_puncture_chain
