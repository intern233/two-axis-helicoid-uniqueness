import TwoAxisHelicoid.AxisHelicoidCalibration
import TwoAxisHelicoid.HeightPeriodNecessity

namespace TwoAxisHelicoid
open Set Complex Filter Bornology
open scoped Topology

/-- The vertical closing equation follows from the actual single-valued
height coordinate with the specified coefficient, without choosing an
integer Gauss branch or assuming either horizontal period closes. -/
theorem harmonic_height_primitive_thetaG_zero {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 = coordinateData t a c ht z 2) :
    thetaG t a = 0 := by
  let L := rhombicPeriodPair t ht
  let f := fun z => puncturedImmersionCoefficient L X z 2
  let u := (L.weierstrassP a).re
  have hu : L.weierstrassP a = (u : ℂ) := by
    apply Complex.ext
    · rfl
    · exact rhombic_weierstrassP_real ht a
  have hP : (ellipticLinePeriod f (-1) (1+I*t)).re = 0 := by
    apply actual_height_primitive_sloping_period_zero ht (F := fun z => X z 2)
    · exact fun z hz => (puncturedImmersionCoefficient_analyticAt hX hz 2).differentiableAt
    · intro z hz
      change HasFDerivAt (fun w => X w 2) (realCoefficientDerivative (puncturedImmersionCoefficient L X z 2)) z
      rw [puncturedImmersionCoefficient_eq hz]
      exact scalarComplexCoefficient_hasFDerivAt ((hX.harmonic z hz 2).1.differentiableAt two_ne_zero)
    · exact fun z hz ω hω => congrFun (hX.periodic z hz ω hω) 2
  have hp : ellipticLinePeriod f (-1) (1+I*t) = heightPeriodHalf t ht c u := by
    unfold ellipticLinePeriod heightPeriodHalf heightLineIntegral
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [show f (-1+(s : ℂ)*(1+I*t)) = coordinateData t a c ht (-1+(s : ℂ)*(1+I*t)) 2 from
      hh _ (rhombic_sloping_line_not_mem ht s)]
    change _ * (I*(c : ℂ)*(L.weierstrassP _-L.weierstrassP a)) = _
    rw [hu]
  have hclose := (height_periods_close_iff_of_pos ht ht hc u).mp
    ⟨heightPeriodTwo_re_zero_of_pos ht ht c u,by rw [← hp]; exact hP⟩
  have hη : thetaEtaExpression t = ((thetaEtaExpression t).re : ℂ) := by
    apply Complex.ext
    · rfl
    · exact thetaEtaExpression_real t
  rw [thetaG_eq_weierstrassP_of_pos ht ht a (real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2])),hu,hclose,hη]
  push_cast
  simp only [Complex.ofReal_re]
  ring

/-- The same global height primitive used in the analytic end chart is
canonically centered at the intersection of the real and imaginary axes. -/
theorem harmonic_height_eq_actualComplexHeight {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hG : thetaG t a = 0) (m : ℤ)
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 = coordinateData t a c ht z 2)
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z) :
    ∀ z ∉ (rhombicPeriodPair t ht).lattice, X z 2 = (actualComplexHeight t a c ht z).re := by
  obtain ⟨b,hb⟩ := harmonic_height_real_primitive ht hX hh
  have hreg := integerAxis_regular_points ht ha (show t ∈ Ioo 0 (2*t) from ⟨ht,by linarith⟩)
  have hm := hb _ hreg.1
  rw [(harmonic_integer_axis_midpoint_data ht ha m hX hg).1,
    closed_actualComplexHeight_midpoint ht ha hG,Complex.zero_re,zero_add] at hm
  intro z hz
  simpa only [← hm,Pi.zero_apply,add_zero] using hb z hz

/-- Every offset produced by the actual exterior height-coordinate identity
is zero. This also pinpoints the origin of the normalization used to apply
the intersection theorem, before using any intersection conclusion. -/
theorem harmonic_integer_exterior_height_offset_zero {t a c b : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hG : thetaG t a = 0) (m : ℤ)
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 = coordinateData t a c ht z 2)
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z)
    {K : ℂ → ℂ} (hK : Tendsto K (cobounded ℂ) (𝓝[≠] 0))
    (hchart : ∀ᶠ ξ in cobounded ℂ, actualComplexHeight t a c ht (K ξ) = ξ)
    (hheight : ∀ᶠ ξ in cobounded ℂ, verticalRotation I (X (K ξ)) 2 = ξ.re+b) :
    b=0 := by
  obtain ⟨ξ,hξ,hξh,hξk⟩ := (hchart.and (hheight.and (hK.eventually
    (rhombic_puncture_eventually_off_lattice ht)))).exists
  change X (K ξ) 2 = ξ.re+b at hξh
  rw [harmonic_height_eq_actualComplexHeight ht ha hG m hX hh hg _ hξk,hξ] at hξh
  linarith

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_integer_exterior_height_offset_zero
