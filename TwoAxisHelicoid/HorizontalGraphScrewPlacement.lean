import TwoAxisHelicoid.HelicoidScrewGraph
import TwoAxisHelicoid.AsymptoticHorizontalRuling
import TwoAxisHelicoid.HorizontalLinePlacement

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace
open scoped Topology ComplexConjugate

private theorem ruling_frame_screw (h : ℝ) (q : Fin 3 → ℝ) :
    let c := Complex.exp ((h:ℂ)*I)
    let unit : ‖c‖=1 := by simp [c,Complex.norm_exp]
    coordinateToTube (lineAxisCoordinates c unit ![0,0,h] q)=helicoidScrewMove (-h) (coordinateToTube q) := by
  dsimp only
  ext
  · change (conj (Complex.exp ((h:ℂ)*I))).re*(q 0-0)-(conj (Complex.exp ((h:ℂ)*I))).im*(q 1-0)=_
    simp [helicoidScrewMove,coordinateToTube]
  · change (conj (Complex.exp ((h:ℂ)*I))).im*(q 0-0)+(conj (Complex.exp ((h:ℂ)*I))).re*(q 1-0)=_
    simp [helicoidScrewMove,coordinateToTube]
  · change q 2-h=q 2+ -h
    rw [sub_eq_add_neg]

/-- Normalizing an arbitrary contained horizontal line uses a screw
symmetry of the physical helicoid. Both orders in the initial complex
coordinate are preserved by this choice of spatial frame. -/
theorem horizontal_graph_screw_placement (L : PeriodPair) (X : PeriodTorus L → Fin 3 → ℝ)
    (closed : IsClosedEmbedding (fun q : PuncturedPeriodTorus L => X q.1))
    (d : ℂ) (hd : ‖d‖=1) (A : Fin 3 → ℝ)
    (line : ∀ r : ℝ, A+r • ![d.re,d.im,0]∈range (fun q : PuncturedPeriodTorus L => X q.1))
    (ver : ∀ r : ℝ, (![0,0,r] : Fin 3 → ℝ)∈range (fun q : PuncturedPeriodTorus L => X q.1))
    (regular : ∀ z∉L.lattice, (∀ j, HarmonicAt (fun w => X (periodTorusProjection L w) j) z) ∧
      ConformalCoordinateDerivatives (X ∘ periodTorusProjection L) z ∧ Function.Injective (fderiv ℝ (X ∘ periodTorusProjection L) z))
    (graph : HasHelicoidC1End (fun q : PuncturedPeriodTorus L => coordinateToTube (X q.1))) :
    let c := Complex.exp (((A 2 : ℝ):ℂ)*I)
    let R := lineAxisCoordinates c (by simp [c,Complex.norm_exp]) ![0,0,A 2]
    let Y := R ∘ X
    IsClosedEmbedding (fun q : PuncturedPeriodTorus L => Y q.1) ∧
    (∀ r : ℝ, (![r,0,0] : Fin 3 → ℝ)∈range (fun q : PuncturedPeriodTorus L => Y q.1)) ∧
    (∀ r : ℝ, (![0,0,r] : Fin 3 → ℝ)∈range (fun q : PuncturedPeriodTorus L => Y q.1)) ∧
    (∀ z∉L.lattice, (∀ j, HarmonicAt (fun w => Y (periodTorusProjection L w) j) z) ∧
      ConformalCoordinateDerivatives (Y ∘ periodTorusProjection L) z ∧ Function.Injective (fderiv ℝ (Y ∘ periodTorusProjection L) z)) ∧
    HasHelicoidC1End (fun q : PuncturedPeriodTorus L => coordinateToTube (Y q.1)) ∧
    meromorphicOrderAt (fun w => immersionComplexCoefficient (Y ∘ periodTorusProjection L) w 2) 0=
      meromorphicOrderAt (fun w => immersionComplexCoefficient (X ∘ periodTorusProjection L) w 2) 0 ∧
    meromorphicOrderAt (immersionGaussLogDerivative (Y ∘ periodTorusProjection L)) 0=
      meromorphicOrderAt (immersionGaussLogDerivative (X ∘ periodTorusProjection L)) 0 := by
  let h := A 2
  let c := Complex.exp ((h:ℂ)*I)
  have unit : ‖c‖=1 := by simp [c,Complex.norm_exp]
  have asym := standard_graph_approaches_ruled closed.continuous graph
  have pa := horizontal_line_tangent_to_ruling asym A d hd line
  rw [one_mul] at pa
  obtain ⟨s,_,hs⟩ := same_span_ruling_vector hd h pa
  have aligned (r : ℝ) : A+r • ![c.re,c.im,0]∈range (fun q : PuncturedPeriodTorus L => X q.1) := by
    simp only [c,Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im]
    change (![Real.cos h,Real.sin h,0] : Fin 3 → ℝ)=_ at hs
    rw [hs,smul_smul]
    exact line _
  let R := lineAxisCoordinates c unit ![0,0,h]
  obtain ⟨_,cl,hor,vert,reg,hh,hg⟩ := horizontal_line_axes_placement L X closed c unit A aligned ver one_ne_zero asym regular
  have newGraph : HasHelicoidC1End (fun q : PuncturedPeriodTorus L => coordinateToTube (R (X q.1))) := by
    have e : (fun q : PuncturedPeriodTorus L => coordinateToTube (R (X q.1)))=
        helicoidScrewMove (-h) ∘ (fun q : PuncturedPeriodTorus L => coordinateToTube (X q.1)) :=
      funext fun q => ruling_frame_screw h _
    rw [e]
    exact graph.screw_motion (coordinateToTube_isProperMap closed.isProperMap) _
  exact ⟨cl,hor,vert,reg,newGraph,hh,hg⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.horizontal_graph_screw_placement
