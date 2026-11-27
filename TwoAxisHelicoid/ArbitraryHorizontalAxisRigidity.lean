import TwoAxisHelicoid.MarkedTorusCertifiedRigidity
import TwoAxisHelicoid.HorizontalLineEndOrders
import TwoAxisHelicoid.HorizontalLineSchwarz

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace
open scoped Topology

/-- A horizontal line is allowed to have arbitrary position, height and
direction. Its intersection with the prescribed vertical axis follows from
Schwarz reflection and from asymptotic containment in the reference helicoid. -/
theorem marked_arbitrary_horizontal_line_similarity_to_certified
    (hHW : RhombicHelicoidIntersectionPrinciple) (L : PeriodPair) (X : PeriodTorus L → Fin 3 → ℝ)
    (hX : IsClosedEmbedding (fun q : PuncturedPeriodTorus L => X q.1))
    (c : ℂ) (hc : ‖c‖ = 1) (A : Fin 3 → ℝ)
    (hline : ∀ r : ℝ, A+r • ![c.re,c.im,0] ∈ range (fun q : PuncturedPeriodTorus L => X q.1))
    (hver : ∀ r : ℝ, (![0,0,r] : Fin 3 → ℝ) ∈ range (fun q : PuncturedPeriodTorus L => X q.1))
    {α : ℝ} (hα : α ≠ 0)
    (hend : ApproachesSetAtInfinity (range (fun q : PuncturedPeriodTorus L => X q.1))
      (range (axisRuledHelicoid I α 0)))
    (hhi : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => X (periodTorusProjection L w) j) z) ∧
      ConformalCoordinateDerivatives (X ∘ periodTorusProjection L) z ∧
      Function.Injective (fderiv ℝ (X ∘ periodTorusProjection L) z))
    (hheight : meromorphicOrderAt (fun w => immersionComplexCoefficient (X ∘ periodTorusProjection L) w 2) 0 = (-2 : ℤ))
    (hgauss : meromorphicOrderAt (immersionGaussLogDerivative (X ∘ periodTorusProjection L)) 0 = (-2 : ℤ)) :
    ∃ (U : PuncturedPeriodTorus L ≃ₜ PuncturedPeriodTorus certifiedPeriodPair)
      (scale : ℝ) (E : EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3))
      (b : EuclideanSpace ℝ (Fin 3)), 0 < scale ∧ ∀ q,
        certifiedTorusImmersion (U q) = scale • E (coordinateToEuclidean (X q.1))+b := by
  obtain ⟨r,hr⟩ := horizontal_half_turn_line_intersects_vertical_axis hα hend hver A
    ![c.re,c.im,0] rfl (embedded_torus_reflects_horizontal_line L X hX c hc A hline hhi)
  let C : Fin 3 → ℝ := ![0,0,A 2]
  let R := lineAxisCoordinates c hc C
  have hhor (s : ℝ) : (![s,0,0] : Fin 3 → ℝ) ∈ range (fun q : PuncturedPeriodTorus L => R (X q.1)) := by
    obtain ⟨q,hq⟩ := hline (r+s)
    have he : A+(r+s) • ![c.re,c.im,0] = C+s • ![c.re,c.im,0] := by
      rw [add_smul,← add_assoc,hr]
    exact ⟨q,(congrArg R (hq.trans he)).trans (lineAxisCoordinates_line c hc C s)⟩
  have hver' (s : ℝ) : (![0,0,s] : Fin 3 → ℝ) ∈ range (fun q : PuncturedPeriodTorus L => R (X q.1)) := by
    obtain ⟨q,hq⟩ := hver (s+A 2)
    refine ⟨q,(congrArg R hq).trans ?_⟩
    ext j
    fin_cases j <;> simp [R,lineAxisCoordinates,C,verticalRotation_apply]
  have hord := lineAxisCoordinates_end_orders c hc C ((punctured_lattice_regular_near_zero L).mono fun z hz =>
    (analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt ((hhi z hz).1 j)).differentiableAt)
  obtain ⟨U,scale,E,b,hs,hE⟩ := marked_straight_axes_similarity_to_certified hHW L (R ∘ X)
    (R.isClosedEmbedding.comp hX) hhor hver'
    (fun z hz => lineAxisCoordinates_harmonic_chart c hc C (hhi z hz).1 (hhi z hz).2.1 (hhi z hz).2.2)
    (hord.1.trans hheight) (hord.2.trans hgauss)
  exact ⟨U,scale,(euclideanOrientationIsometry R (lineAxisCoordinates_dist_sq c hc C)).trans E,b,hs,hE⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.marked_arbitrary_horizontal_line_similarity_to_certified
