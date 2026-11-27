import TwoAxisHelicoid.MarkedHelicoidGaussPole
import TwoAxisHelicoid.MarkedHelicoidIntersectionTheorem
import TwoAxisHelicoid.MarkedTorusCertifiedRigidity
import TwoAxisHelicoid.HelicoidEndReparameterization

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace
open scoped Topology

/-- An arbitrary marked embedded punctured complex torus with the two
standard straight axes and a proper helicoidal normal graph in the
standard spatial frame is the certified torus up to a positive
similarity. The torus lattice, both end orders, branch and periods are
determined from the given immersion. -/
theorem marked_helicoid_graph_similarity_to_certified (L : PeriodPair) (X : PeriodTorus L → Fin 3 → ℝ)
    (hX : IsClosedEmbedding (fun q : PuncturedPeriodTorus L => X q.1))
    (hhor : ∀ s : ℝ, (![s,0,0] : Fin 3 → ℝ)∈range (fun q : PuncturedPeriodTorus L => X q.1))
    (hver : ∀ s : ℝ, (![0,0,s] : Fin 3 → ℝ)∈range (fun q : PuncturedPeriodTorus L => X q.1))
    (hhi : ∀ z∉L.lattice, (∀ j, HarmonicAt (fun w => X (periodTorusProjection L w) j) z) ∧
      ConformalCoordinateDerivatives (X ∘ periodTorusProjection L) z ∧
      Function.Injective (fderiv ℝ (X ∘ periodTorusProjection L) z))
    (graph : HasHelicoidC1End (fun q : PuncturedPeriodTorus L => coordinateToTube (X q.1))) :
    ∃ (U : PuncturedPeriodTorus L ≃ₜ PuncturedPeriodTorus certifiedPeriodPair)
      (scale : ℝ) (E : EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3))
      (b : EuclideanSpace ℝ (Fin 3)), 0<scale ∧ ∀ q,
        certifiedTorusImmersion (U q)=scale • E (coordinateToEuclidean (X q.1))+b := by
  obtain ⟨s,t,hs,ht,hp,hY⟩ := straight_axes_to_two_axis_harmonic_immersion L X hX hhor hver hhi
  let M := rhombicPeriodPair t ht
  obtain ⟨e,he⟩ := scaled_harmonic_quotient_correspondence L M s hs hp X hY
  have same : (fun q : PuncturedPeriodTorus L => X q.1) ∘ e.symm=harmonicTorusImmersion hY := by
    funext q
    simpa only [e.apply_symm_apply,Function.comp_apply] using (he (e.symm q)).symm
  have hg : HasHelicoidC1End (coordinateToTube ∘ harmonicTorusImmersion hY) := by
    rw [← same]
    exact graph.comp_homeomorph e.symm
  have closed : IsClosedEmbedding (harmonicTorusImmersion hY) := same ▸ hX.comp e.symm.isClosedEmbedding
  obtain ⟨hh,gauss⟩ := marked_helicoid_two_double_poles ht hY closed.isProperMap hg
  obtain ⟨U,k,A,b,hk,h⟩ := harmonic_meromorphic_similarity_to_certified_torus marked_rhombic_helicoid_intersection
    ht hY closed.injective hh.2 gauss.2
  exact ⟨e.trans U,k,A,b,hk,fun q => (h (e q)).trans (by rw [he])⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_helicoid_graph_similarity_to_certified
