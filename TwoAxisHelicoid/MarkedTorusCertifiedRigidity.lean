import TwoAxisHelicoid.SchwarzNormalizedImmersion
import TwoAxisHelicoid.TorusEndScalingOrders
import TwoAxisHelicoid.ScaledTorusImmersion
import TwoAxisHelicoid.HoffmanWhiteModelRigidity

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace
open scoped Topology

/-- Starting with any marked punctured complex torus, the two spatial lines,
the regular harmonic conformal immersion and the two intrinsic end orders
determine the whole immersion up to similarity. The intersection result of
Hoffman--White remains a named literature hypothesis. -/
theorem marked_straight_axes_similarity_to_certified (hHW : RhombicHelicoidIntersectionPrinciple)
    (L : PeriodPair) (X : PeriodTorus L → Fin 3 → ℝ)
    (hX : IsClosedEmbedding (fun q : PuncturedPeriodTorus L => X q.1))
    (hhor : ∀ s : ℝ, (![s,0,0] : Fin 3 → ℝ) ∈ range (fun q : PuncturedPeriodTorus L => X q.1))
    (hver : ∀ s : ℝ, (![0,0,s] : Fin 3 → ℝ) ∈ range (fun q : PuncturedPeriodTorus L => X q.1))
    (hhi : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => X (periodTorusProjection L w) j) z) ∧
      ConformalCoordinateDerivatives (X ∘ periodTorusProjection L) z ∧
      Function.Injective (fderiv ℝ (X ∘ periodTorusProjection L) z))
    (hheight : meromorphicOrderAt (fun w => immersionComplexCoefficient (X ∘ periodTorusProjection L) w 2) 0 = (-2 : ℤ))
    (hgauss : meromorphicOrderAt (immersionGaussLogDerivative (X ∘ periodTorusProjection L)) 0 = (-2 : ℤ)) :
    ∃ (U : PuncturedPeriodTorus L ≃ₜ PuncturedPeriodTorus certifiedPeriodPair)
      (scale : ℝ) (E : EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3))
      (b : EuclideanSpace ℝ (Fin 3)), 0 < scale ∧ ∀ q,
        certifiedTorusImmersion (U q) = scale • E (coordinateToEuclidean (X q.1))+b := by
  obtain ⟨s,t,hs,ht,hp,hY⟩ := straight_axes_to_two_axis_harmonic_immersion L X hX hhor hver hhi
  let M := rhombicPeriodPair t ht
  obtain ⟨e,he⟩ := scaled_harmonic_quotient_correspondence L M s hs hp X hY
  have hi : Function.Injective (harmonicTorusImmersion hY) := by
    intro q r h
    obtain ⟨u,rfl⟩ := e.surjective q
    obtain ⟨v,rfl⟩ := e.surjective r
    exact congrArg e (hX.injective ((he u).symm.trans (h.trans (he v))))
  obtain ⟨hh,hg⟩ := marked_torus_scaled_end_orders L M (X ∘ periodTorusProjection L) s⁻¹
    (inv_ne_zero hs) (fun z hz => ⟨(hhi z hz).1,(hhi z hz).2.1⟩) hheight hgauss
  obtain ⟨U,scale,E,b,hscale,hU⟩ :=
    harmonic_meromorphic_similarity_to_certified_torus hHW ht hY hi hh hg
  exact ⟨e.trans U,scale,E,b,hscale,fun q => (hU (e q)).trans (by rw [he])⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.marked_straight_axes_similarity_to_certified
