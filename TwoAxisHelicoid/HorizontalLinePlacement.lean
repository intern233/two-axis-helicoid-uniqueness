import TwoAxisHelicoid.HorizontalLineEndOrders
import TwoAxisHelicoid.HorizontalLineSchwarz

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace
open scoped Topology

/-- Rotate and translate the actual horizontal straight line to the standard
axis. Analytic regularity and both meromorphic orders are in the same
coordinate system as the transformed embedded image. -/
theorem horizontal_line_axes_placement (L : PeriodPair) (X : PeriodTorus L → Fin 3 → ℝ)
    (hX : IsClosedEmbedding (fun q : PuncturedPeriodTorus L => X q.1))
    (c : ℂ) (hc : ‖c‖ = 1) (A : Fin 3 → ℝ)
    (hline : ∀ r : ℝ, A+r • ![c.re,c.im,0] ∈ range (fun q : PuncturedPeriodTorus L => X q.1))
    (hver : ∀ r : ℝ, (![0,0,r] : Fin 3 → ℝ) ∈ range (fun q : PuncturedPeriodTorus L => X q.1))
    {α : ℝ} (hα : α ≠ 0)
    (hend : ApproachesSetAtInfinity (range (fun q : PuncturedPeriodTorus L => X q.1))
      (range (axisRuledHelicoid I α 0)))
    (hhi : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => X (periodTorusProjection L w) j) z) ∧
      ConformalCoordinateDerivatives (X ∘ periodTorusProjection L) z ∧
      Function.Injective (fderiv ℝ (X ∘ periodTorusProjection L) z)) :
    let R := lineAxisCoordinates c hc (![0,0,A 2]:Fin 3 → ℝ)
    let Y := R ∘ X
    (∃ r : ℝ, A+r • ![c.re,c.im,0] = ![0,0,A 2]) ∧
    IsClosedEmbedding (fun q : PuncturedPeriodTorus L => Y q.1) ∧
    (∀ s : ℝ, (![s,0,0] : Fin 3 → ℝ) ∈ range (fun q : PuncturedPeriodTorus L => Y q.1)) ∧
    (∀ s : ℝ, (![0,0,s] : Fin 3 → ℝ) ∈ range (fun q : PuncturedPeriodTorus L => Y q.1)) ∧
    (∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => Y (periodTorusProjection L w) j) z) ∧
      ConformalCoordinateDerivatives (Y ∘ periodTorusProjection L) z ∧
      Function.Injective (fderiv ℝ (Y ∘ periodTorusProjection L) z)) ∧
    meromorphicOrderAt (fun w => immersionComplexCoefficient (Y ∘ periodTorusProjection L) w 2) 0 =
      meromorphicOrderAt (fun w => immersionComplexCoefficient (X ∘ periodTorusProjection L) w 2) 0 ∧
    meromorphicOrderAt (immersionGaussLogDerivative (Y ∘ periodTorusProjection L)) 0 =
      meromorphicOrderAt (immersionGaussLogDerivative (X ∘ periodTorusProjection L)) 0 := by
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
  exact ⟨⟨r,hr⟩,R.isClosedEmbedding.comp hX,hhor,hver',
    fun z hz => lineAxisCoordinates_harmonic_chart c hc C (hhi z hz).1 (hhi z hz).2.1 (hhi z hz).2.2,hord⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.horizontal_line_axes_placement
