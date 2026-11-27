import TwoAxisHelicoid.GeneralBBCExteriorGerm
import TwoAxisHelicoid.HeightGaussEndNormalForm
import TwoAxisHelicoid.ExteriorHeightGaussPoles

namespace TwoAxisHelicoid
open Complex Set Filter Topology Bornology
open scoped Topology ContDiff Manifold

/-- The logarithmic differential in the original exterior height chart
can be recovered directly from its measured exponential Gauss map. Its
leading coefficient is nonzero and its error is the derivative of the
actual holomorphic correction. -/
noncomputable def GeometricExteriorCoordinate.toFiniteTopologyDifferential
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] {X : M → Fin 3 → ℝ}
    (D : GeometricExteriorCoordinate X) : FiniteTopologyExteriorDifferential X := by
  let G := fun w : ℂ => immersionGaussMap (X ∘ D.chart.symm) w⁻¹
  let k := I*(D.pitch:ℂ)
  have nk : k≠0 := mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr D.pitch_ne)
  have agrees : G =ᶠ[𝓝[≠] (0:ℂ)] fun w => exp (k/w+D.correction w) := by
    filter_upwards [tendsto_inv₀_nhdsNE_zero.eventually D.gauss] with w hw
    simpa only [G,k,div_eq_mul_inv,inv_inv] using hw
  have data : ∀ᶠ w in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ G w ∧ G w≠0 ∧
      logDeriv G w=(-k)/w^2+deriv D.correction w := by
    filter_upwards [punctured_germ_eventually_local agrees,D.analytic.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with w he an nz
    change w≠0 at nz
    have di : HasDerivAt (fun z : ℂ => k/z) ((-k)/w^2) w := by
      simpa only [zero_mul,mul_one,zero_sub,id_eq,Pi.div_def] using! (hasDerivAt_const w k).div (hasDerivAt_id w) nz
    have de : HasDerivAt (fun x : ℂ => exp (k/x+D.correction x))
        (exp (k/w+D.correction w)*(-k/w^2+deriv D.correction w)) w := (di.add an.differentiableAt.hasDerivAt).cexp
    refine ⟨de.differentiableAt.congr_of_eventuallyEq he,he.self_of_nhds ▸ exp_ne_zero _,?_⟩
    change deriv G w/G w=_
    rw [he.deriv_eq,he.self_of_nhds,de.deriv]
    exact mul_div_cancel_left₀ _ (exp_ne_zero _)
  have pole := analytic_double_pole_with_remainder (neg_ne_zero.mpr nk) D.analytic.deriv (data.mono fun _ h => h.2.2)
  refine ⟨D.chart,D.radius,D.positive,D.target,D.core,D.holomorphic,D.heightOffset,D.height,
    D.pitch,deriv D.correction,D.analytic.deriv,pole.2,?_⟩
  filter_upwards [data] with w hw
  refine ⟨hw.1,hw.2.1,?_⟩
  change logDeriv G w-k*((-1:ℂ)/w^2)=deriv D.correction w
  rw [hw.2.2]
  ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.GeometricExteriorCoordinate.toFiniteTopologyDifferential
