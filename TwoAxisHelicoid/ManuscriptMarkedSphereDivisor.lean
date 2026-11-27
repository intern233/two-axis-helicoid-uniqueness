import TwoAxisHelicoid.AlignedEndDoublePoles
import TwoAxisHelicoid.HarmonicNullLift
import TwoAxisHelicoid.NullGaussDivisor
import TwoAxisHelicoid.SphericalNullGauss
import Mathlib.Analysis.Calculus.Deriv.Inverse

namespace TwoAxisHelicoid
open Complex Set Filter Topology Bornology
open scoped OnePoint Topology

private theorem position_spherical_gauss_continuous {L : PeriodPair} {Z : ℂ → Fin 3 → ℝ}
    (hZ : TwoAxisHarmonicConformalImmersion L Z) {z : ℂ} (hz : z ∉ L.lattice) :
    ContinuousAt (fun w => sphericalNullGauss (immersionComplexCoefficient Z w)) z := by
  have near := L.isClosed_lattice.isOpen_compl.mem_nhds hz
  have regular : puncturedImmersionCoefficient L Z z ≠ 0 := by
    rw [puncturedImmersionCoefficient_eq hz]
    exact immersionComplexCoefficient_regular (hZ.differentiable z hz) (hZ.immersion z hz)
  have nullNear : ∀ᶠ w in 𝓝 z, ComplexNull (puncturedImmersionCoefficient L Z w) := by
    filter_upwards [near] with w hw
    rw [puncturedImmersionCoefficient_eq hw]
    exact immersionComplexCoefficient_null (hZ.conformal w hw)
  have h := sphericalNullGauss_continuousAt (u := puncturedImmersionCoefficient L Z)
    (fun j => (puncturedImmersionCoefficient_analyticAt hZ hz j).continuousAt)
    regular nullNear
  apply h.congr_of_eventuallyEq
  filter_upwards [near] with w hw
  exact congrArg sphericalNullGauss (puncturedImmersionCoefficient_eq (X := Z) hw).symm

/-- In the very marking of the physical immersion's simple divisor, its sphere-valued
Gauss map takes the south and north stereographic values at the two signed points. -/
theorem manuscript_physical_spherical_gauss_divisor {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 1)
    {Z : ℂ → Fin 3 → ℝ} (hZ : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) Z)
    (divisor : GaussZeroPoleData t a ht (immersionGaussMap Z)) :
    sphericalNullGauss (immersionComplexCoefficient Z (a:ℂ)) = (↑(0:ℂ) : OnePoint ℂ) ∧
      sphericalNullGauss (immersionComplexCoefficient Z (-(a:ℂ))) = ∞ := by
  let g := immersionGaussMap Z
  let G := fun z => sphericalNullGauss (immersionComplexCoefficient Z z)
  have chart (z : ℂ) (hn : g z ≠ 0) : G z = (↑(g z) : OnePoint ℂ) := by
    have hminus : nullHorizontalMinus (immersionComplexCoefficient Z z) ≠ 0 := by
      intro h
      exact hn (by simp [g,immersionGaussMap,nullGauss,h])
    simp only [G,g,sphericalNullGauss,ite_eq_right hminus,immersionGaussMap]
  have haL := real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2] : a < 2)
  have hnegL : -(a:ℂ) ∉ (rhombicPeriodPair t ht).lattice := by simpa using haL
  constructor
  · have c : Tendsto g (𝓝[≠] (a:ℂ)) (𝓝 0) := by
      simpa only [g,divisor.positive_zero] using
        (divisor.positive_analytic.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    have nz : ∀ᶠ z in 𝓝[≠] (a:ℂ), g z ≠ 0 :=
      divisor.positive_analytic.differentiableAt.hasDerivAt.eventually_ne divisor.positive_simple
    have limit : Tendsto G (𝓝[≠] (a:ℂ)) (𝓝 (↑(0:ℂ) : OnePoint ℂ)) :=
      (OnePoint.continuous_coe.continuousAt.tendsto.comp c).congr' (nz.mono fun z hz => (chart z hz).symm)
    exact tendsto_nhds_unique ((position_spherical_gauss_continuous hZ haL).tendsto.mono_left nhdsWithin_le_nhds) limit
  · have inverseAtZero : Tendsto (fun w : ℂ => (↑(w⁻¹) : OnePoint ℂ)) (𝓝[≠] 0) (𝓝 ∞) := by
      apply OnePoint.tendsto_coe_infty.comp
      rw [coclosedCompact_eq_cocompact,← Metric.cobounded_eq_cocompact]
      exact Filter.tendsto_inv₀_nhdsNE_zero
    have d := divisor.negative_analytic.differentiableAt.hasDerivAt
    have invLimit : Tendsto (fun w => (g w)⁻¹) (𝓝[≠] (-(a:ℂ))) (𝓝[≠] (0:ℂ)) := by
      simpa only [g,divisor.negative_zero] using d.tendsto_nhdsNE divisor.negative_simple
    have c : Tendsto (fun w => (↑(g w) : OnePoint ℂ)) (𝓝[≠] (-(a:ℂ))) (𝓝 ∞) := by
      simpa only [Function.comp_def,inv_inv] using inverseAtZero.comp invLimit
    have nz : ∀ᶠ w in 𝓝[≠] (-(a:ℂ)), g w ≠ 0 := by
      have h : ∀ᶠ w in 𝓝[≠] (-(a:ℂ)), (g w)⁻¹ ≠ 0 := d.eventually_ne divisor.negative_simple
      simpa only [ne_eq,inv_eq_zero] using h
    have limit : Tendsto G (𝓝[≠] (-(a:ℂ))) (𝓝 ∞) := c.congr' (nz.mono fun z hz => (chart z hz).symm)
    exact tendsto_nhds_unique ((position_spherical_gauss_continuous hZ hnegL).tendsto.mono_left nhdsWithin_le_nhds) limit

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.manuscript_physical_spherical_gauss_divisor
