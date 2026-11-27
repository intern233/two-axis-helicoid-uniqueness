import TwoAxisHelicoid.WeierstrassControlledTails
import TwoAxisHelicoid.AnalyticEndGeodesic

namespace TwoAxisHelicoid
open Complex Real Set Filter Bornology

/-- Analytic helicoidal end data and thinness suffice for the actual
controlled tangent curves. All geodesic and acceleration inputs have been
discharged by the preceding ODE and Weierstrass calculations. -/
theorem analytic_helicoidal_thin_end_controlled_curves
    {X : ℂ → Fin 3 → ℝ} {f : ℂ → ℂ} (α R₀ : ℝ)
    (hf : AnalyticAt ℂ f 0)
    (hX : ∀ z : ℂ, R₀ < ‖z‖ → HasFDerivAt X
      (nullRealDerivative (weierstrassTriple (exp (I*(α : ℂ)*z+infinityCorrection f z)) 1)) z)
    (hthin : ∀ ε : ℝ, 0 < ε → ∃ S : ℝ, ∀ z : ℂ, S < ‖z‖ →
      coordinateToTube (X z) ∈ helicoidTubeEquiv.target ∧
      |helicoidSignedDistance (coordinateToTube (X z))| ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 → ∃ T : ℝ, 0 < T ∧ ∀ z : ℂ, T < ‖z‖ →
      HasControlledUnitTangentCurves (coordinateToTube (X z))
        (coordinateToTube.comp (nullRealDerivative
          (weierstrassTriple (exp (I*(α : ℂ)*z+infinityCorrection f z)) 1))) ε (|α|+1) := by
  obtain ⟨R,hRbase,hR0,hcontrol,_hgeodesic⟩ := analytic_helicoidal_end_unit_geodesics α R₀ hf
  exact holomorphic_thin_end_controlled_tangent_curves hR0.le (by positivity)
    (fun z hz => (hcontrol z hz).1) (fun z hz => (hcontrol z hz).2)
    (fun z hz => hX z (hRbase.trans hz)) hthin

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.analytic_helicoidal_thin_end_controlled_curves
