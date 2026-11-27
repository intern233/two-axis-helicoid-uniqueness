import TwoAxisHelicoid.RuledMinimalGraph
import TwoAxisHelicoid.ConformalMinimalGraphContact
import TwoAxisHelicoid.PlanarDriftFactor

namespace TwoAxisHelicoid
open Complex Filter Set Topology InnerProductSpace
open scoped Topology ContDiff

/-- Signed side of a ruled surface in coordinates (ruling parameter,
height, graph height). -/
def ruledGraphSide (C S : ℝ → ℝ) (p : Fin 3 → ℝ) := C (p 1)*p 2+S (p 1)*p 0

/-- In ruling coordinates a locally nonsingular trigonometric coefficient
gives a nonvanishing analytic factor times a minimal-graph difference. -/
theorem harmonic_chart_ruled_drift_factor {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (reg : ∀ᶠ w in 𝓝 z, (∀ j, HarmonicAt (fun u => X u j) w) ∧ ConformalCoordinateDerivatives X w)
    (inj : Function.Injective (fderiv ℝ X z)) (C S : ℝ → ℝ) (k : ℝ)
    (aC : ∀ y, AnalyticAt ℝ C y) (aS : ∀ y, AnalyticAt ℝ S y)
    (dC : ∀ y, HasDerivAt C (-k*S y) y) (dS : ∀ y, HasDerivAt S (k*C y) y)
    (nc : C (X z 1) ≠ 0) :
    HasPlanarDriftFactorAt (fun w => ruledGraphSide C S (X w)) z := by
  let a := fun h => -(S h)/C h
  let g := ruledCartesianHeight a
  let f := immersionGraphDifference X g
  let P := spatialGraphProjection 0 1
  have ja {y : ℝ} (ny : C y ≠ 0) : AnalyticAt ℝ a y := (aS y).neg.div (aC y) ny
  have ode {y : ℝ} (ny : C y ≠ 0) : HasDerivAt a (-k*(1+(a y)^2)) y := by
    have h := (dS y).neg.div (dC y) ny
    convert h using 1
    dsimp [a]
    field_simp
    ring
  have rg (p : ℂ) (np : C p.im ≠ 0) : cartesianMinimalGraphOperator g p=0 := by
    apply ruled_height_minimal_of_riccati (-k) (ja np)
    filter_upwards [(aC p.im).continuousAt.eventually_ne np] with y ny
    exact ode ny
  have ax : AnalyticAt ℝ X z := analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (reg.self_of_nhds.1 j)
  have ac : AnalyticAt ℝ (fun w => C (X w 1)) z := (aC _).comp ((analyticAt_pi_iff.mp ax) 1)
  have factor {w : ℂ} (nw : C (X w 1) ≠ 0) : ruledGraphSide C S (X w)=C (X w 1)*f w := by
    change C _*X w 2+S _*X w 0=C _*(X w 2-X w 0*(-S (X w 1)/C (X w 1)))
    field_simp
    ring
  have base : C (P (X z)).im ≠ 0 := nc
  have near : ∀ᶠ p in 𝓝 (P (X z)), C p.im ≠ 0 :=
    ((aC _).continuousAt.comp (f := Complex.im) imCLM.continuous.continuousAt).eventually_ne base
  have ag := ruledCartesianHeight_analytic (ja base)
  obtain ⟨A,B,ca,cb,eq⟩ := harmonic_immersion_graph_difference_local_drift reg inj ag (near.mono rg)
  exact ⟨_,f,A,B,ac,nc,immersionGraphDifference_analytic ax ag,ca,cb,(ac.continuousAt.eventually_ne nc).mono (fun _ nw => factor nw),eq⟩

/-- A harmonic conformal immersion locally lying on one side of a
comparison helicoid must have its image locally in that helicoid. The
argument is in the sheet's own parameters and allows a vertical
tangent plane. -/
theorem harmonic_chart_one_sided_ruled_contact {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (reg : ∀ᶠ w in 𝓝 z, (∀ j, HarmonicAt (fun u => X u j) w) ∧ ConformalCoordinateDerivatives X w)
    (inj : Function.Injective (fderiv ℝ X z)) (C S : ℝ → ℝ) (k : ℝ)
    (aC : ∀ y, AnalyticAt ℝ C y) (aS : ∀ y, AnalyticAt ℝ S y)
    (dC : ∀ y, HasDerivAt C (-k*S y) y) (dS : ∀ y, HasDerivAt S (k*C y) y)
    (nc : C (X z 1) ≠ 0) (on : ruledGraphSide C S (X z)=0)
    (side : (∀ᶠ w in 𝓝 z, 0 ≤ ruledGraphSide C S (X w)) ∨ (∀ᶠ w in 𝓝 z, ruledGraphSide C S (X w) ≤ 0)) :
    ∀ᶠ w in 𝓝 z, ruledGraphSide C S (X w)=0 := by
  exact (harmonic_chart_ruled_drift_factor reg inj C S k aC aS dC dS nc).interior_contact on side

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_chart_ruled_drift_factor
#print axioms TwoAxisHelicoid.harmonic_chart_one_sided_ruled_contact
