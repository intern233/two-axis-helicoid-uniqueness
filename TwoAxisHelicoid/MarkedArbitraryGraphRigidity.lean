import TwoAxisHelicoid.MarkedGraphCertifiedRigidity
import TwoAxisHelicoid.HorizontalGraphScrewPlacement

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace
open scoped Topology

/-- The complete horizontal line may have arbitrary height, direction
and initial point. Its recentering is an actual screw symmetry of the
asymptote. No pole order or reflection is assumed. -/
theorem marked_arbitrary_horizontal_graph_similarity (L : PeriodPair) (X : PeriodTorus L → Fin 3 → ℝ)
    (closed : IsClosedEmbedding (fun q : PuncturedPeriodTorus L => X q.1))
    (d : ℂ) (hd : ‖d‖=1) (A : Fin 3 → ℝ)
    (line : ∀ r : ℝ, A+r • ![d.re,d.im,0]∈range (fun q : PuncturedPeriodTorus L => X q.1))
    (ver : ∀ r : ℝ, (![0,0,r] : Fin 3 → ℝ)∈range (fun q : PuncturedPeriodTorus L => X q.1))
    (regular : ∀ z∉L.lattice, (∀ j, HarmonicAt (fun w => X (periodTorusProjection L w) j) z) ∧
      ConformalCoordinateDerivatives (X ∘ periodTorusProjection L) z ∧ Function.Injective (fderiv ℝ (X ∘ periodTorusProjection L) z))
    (graph : HasHelicoidC1End (fun q : PuncturedPeriodTorus L => coordinateToTube (X q.1))) :
    ∃ (U : PuncturedPeriodTorus L ≃ₜ PuncturedPeriodTorus certifiedPeriodPair)
      (scale : ℝ) (E : EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3))
      (b : EuclideanSpace ℝ (Fin 3)), 0<scale ∧ ∀ q,
        certifiedTorusImmersion (U q)=scale • E (coordinateToEuclidean (X q.1))+b := by
  let h := A 2
  let c := Complex.exp ((h:ℂ)*I)
  have unit : ‖c‖=1 := by simp [c,Complex.norm_exp]
  let R := lineAxisCoordinates c unit ![0,0,h]
  obtain ⟨cl,hor,vert,reg,newGraph,_,_⟩ := horizontal_graph_screw_placement L X closed d hd A line ver regular graph
  obtain ⟨U,k,B,b,hk,eq⟩ := marked_helicoid_graph_similarity_to_certified L (R ∘ X) cl hor vert reg newGraph
  let E := euclideanOrientationIsometry R (lineAxisCoordinates_dist_sq c unit ![0,0,h])
  exact ⟨U,k,E.trans B,b,hk,eq⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_arbitrary_horizontal_graph_similarity
