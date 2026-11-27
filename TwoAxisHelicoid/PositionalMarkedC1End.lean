import TwoAxisHelicoid.HorizontalLinePlacement
import TwoAxisHelicoid.SchwarzNormalizedImmersion
import TwoAxisHelicoid.ScaledTorusImmersion
import TwoAxisHelicoid.TorusEndScalingOrders
import TwoAxisHelicoid.HarmonicMeromorphicC1End
import TwoAxisHelicoid.HelicoidEndReparameterization

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace

/-- Two embedded straight lines, the analytic pole orders and one-sided
positional asymptotics imply an actual global C¹ helicoidal end before
using the intersection theorem or selecting an integer branch. -/
theorem positional_marked_torus_has_helicoidal_graph (L : PeriodPair) (X : PeriodTorus L → Fin 3 → ℝ)
    (hX : IsClosedEmbedding (fun q : PuncturedPeriodTorus L => X q.1))
    (c : ℂ) (hc : ‖c‖ = 1) (A : Fin 3 → ℝ)
    (hline : ∀ r : ℝ, A+r • ![c.re,c.im,0] ∈ range (fun q : PuncturedPeriodTorus L => X q.1))
    (hver : ∀ r : ℝ, (![0,0,r] : Fin 3 → ℝ) ∈ range (fun q : PuncturedPeriodTorus L => X q.1))
    {α : ℝ} (hα : α ≠ 0) (hend : ApproachesSetAtInfinity (range (fun q : PuncturedPeriodTorus L => X q.1))
      (range (axisRuledHelicoid I α 0)))
    (hhi : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => X (periodTorusProjection L w) j) z) ∧
      ConformalCoordinateDerivatives (X ∘ periodTorusProjection L) z ∧
      Function.Injective (fderiv ℝ (X ∘ periodTorusProjection L) z))
    (hheight : meromorphicOrderAt (fun z => immersionComplexCoefficient (X ∘ periodTorusProjection L) z 2) 0 = (-2:ℤ))
    (hgauss : meromorphicOrderAt (immersionGaussLogDerivative (X ∘ periodTorusProjection L)) 0 = (-2:ℤ)) :
    HasHelicoidalC1End (fun q : PuncturedPeriodTorus L => X q.1) := by
  let C : Fin 3 → ℝ := ![0,0,A 2]
  let R := lineAxisCoordinates c hc C
  let Y := R ∘ X
  obtain ⟨_,hY,hh,hv,hreg,h₁,h₂⟩ := horizontal_line_axes_placement L X hX c hc A hline hver hα hend hhi
  obtain ⟨s,t,hs,ht,hp,hZ⟩ := straight_axes_to_two_axis_harmonic_immersion L Y hY hh hv hreg
  let M := rhombicPeriodPair t ht
  obtain ⟨e,he⟩ := scaled_harmonic_quotient_correspondence L M s hs hp Y hZ
  obtain ⟨h₃,h₄⟩ := marked_torus_scaled_end_orders L M (Y ∘ periodTorusProjection L) s⁻¹
    (inv_ne_zero hs) (fun z hz => ⟨(hreg z hz).1,(hreg z hz).2.1⟩) (h₁.trans hheight) (h₂.trans hgauss)
  have h := (harmonic_meromorphic_torus_C1_helicoidal_end ht hZ h₃ h₄).comp_homeomorph e
  have eq : harmonicTorusImmersion hZ ∘ e = R ∘ (fun q : PuncturedPeriodTorus L => X q.1) := funext he
  rw [eq] at h
  exact HasHelicoidalC1End.of_isometry R (lineAxisCoordinates_dist_sq c hc C) h

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positional_marked_torus_has_helicoidal_graph
