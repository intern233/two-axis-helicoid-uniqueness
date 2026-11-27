import TwoAxisHelicoid.MarkedEmbeddedPitchFamily
import TwoAxisHelicoid.OriginalHelicoidRepresentative
import TwoAxisHelicoid.HorizontalLineEndOrders
import TwoAxisHelicoid.HorizontalLineSchwarz

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace
open scoped Topology ContDiff Manifold

/-- Put a geometric candidate with an arbitrarily placed horizontal axis
into the unit-pitch family, before any use of horizontal root bounds. -/
theorem original_representative_in_pitch_family (surface : OriginalHelicoidRepresentative)
    (bbc : OriginalHelicoidExteriorPrinciple) (uniform : CompactGenusOneUniformization.{0} surface.modelTorus)
    (hw : RhombicHelicoidIntersectionPrinciple) :
    ∃ W ∈ embeddedPitchFamily, (spatialSimilaritySetoid _).r surface.image W.image := by
  have transfer {e : OpenPartialHomeomorph surface.carrier ℂ} (he : InducedIsothermalChart surface.position e) :
      HarmonicImmersionChart surface.position e :=
    real_minimal_isothermal_chart_harmonic surface.smooth surface.immersion surface.minimal he
  obtain ⟨S,hs,hchart,⟨Aend⟩⟩ := bbc surface
  let := S
  let := hs
  obtain ⟨L,f,Y,_,_,hf,hclose,him,reg,hh,hg⟩ := original_surface_from_arbitrary_exterior_frame surface.topologicalType
    uniform surface.position surface.closedEmbedding (fun e he => transfer (hchart e he)) Aend surface.axes.pitch_ne surface.positional.1
  let c := surface.axes.horizontalDirection
  let P := surface.axes.horizontalPoint
  let F := fun q : PuncturedPeriodTorus L => Y q.1
  have hline : ∀ r : ℝ, P+r • ![c.re,c.im,0] ∈ range F := him.symm ▸ surface.axes.horizontal
  have hver : ∀ r : ℝ, (![0,0,r] : Fin 3 → ℝ) ∈ range F := him.symm ▸ surface.axes.vertical
  obtain ⟨r,hr⟩ := horizontal_half_turn_line_intersects_vertical_axis surface.axes.pitch_ne (him.symm ▸ surface.positional.1) hver P
    ![c.re,c.im,0] rfl (embedded_torus_reflects_horizontal_line L Y hclose c surface.axes.unit P hline reg)
  let C : Fin 3 → ℝ := ![0,0,P 2]
  let R := lineAxisCoordinates c surface.axes.unit C
  have hhor (u : ℝ) : (![u,0,0] : Fin 3 → ℝ) ∈ range (R ∘ F) := by
    obtain ⟨q,hq⟩ := hline (r+u)
    have e : P+(r+u) • ![c.re,c.im,0] = C+u • ![c.re,c.im,0] := by rw [add_smul,← add_assoc,hr]
    exact ⟨q,(congrArg R (hq.trans e)).trans (lineAxisCoordinates_line c surface.axes.unit C u)⟩
  have hver' (u : ℝ) : (![0,0,u] : Fin 3 → ℝ) ∈ range (R ∘ F) := by
    obtain ⟨q,hq⟩ := hver (u+P 2)
    refine ⟨q,(congrArg R hq).trans ?_⟩
    ext j
    fin_cases j <;> simp [R,lineAxisCoordinates,C,verticalRotation_apply]
  have hord := lineAxisCoordinates_end_orders c surface.axes.unit C ((punctured_lattice_regular_near_zero L).mono fun z hz =>
    (analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt ((reg z hz).1 j)).differentiableAt)
  obtain ⟨W,hW,_,hS⟩ := marked_embedded_pitch_normalization hw L (R ∘ Y) (R.isClosedEmbedding.comp hclose)
    hhor hver' (fun z hz => lineAxisCoordinates_harmonic_chart c surface.axes.unit C (reg z hz).1 (reg z hz).2.1 (reg z hz).2.2)
    (hord.1.trans hh) (hord.2.trans hg)
  let E := euclideanOrientationIsometry R (lineAxisCoordinates_dist_sq c surface.axes.unit C)
  have ha : (spatialSimilaritySetoid _).r surface.image (range (fun q : PuncturedPeriodTorus L => coordinateToEuclidean (R (Y q.1)))) := by
    apply image_similarity_of_surjective_parameters surface.euclideanPosition _ f f.surjective 1 E 0 one_pos
    intro x
    simp only [hf,one_smul,add_zero]
    rfl
  exact ⟨W,hW,(spatialSimilaritySetoid _).trans ha hS⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_representative_in_pitch_family
