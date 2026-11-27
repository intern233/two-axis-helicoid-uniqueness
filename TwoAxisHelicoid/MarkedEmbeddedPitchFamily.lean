import TwoAxisHelicoid.EmbeddedPitchFamily
import TwoAxisHelicoid.SchwarzNormalizedImmersion
import TwoAxisHelicoid.TorusEndScalingOrders
import TwoAxisHelicoid.ScaledTorusImmersion

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace

/-- Obtain the Appendix B normalized representative starting on an
arbitrary marked complex torus. The original image, the modulus and the
change of lattice are retained. The proof uses no horizontal sign bound. -/
theorem marked_embedded_pitch_normalization (hw : RhombicHelicoidIntersectionPrinciple)
    (L : PeriodPair) (X : PeriodTorus L → Fin 3 → ℝ)
    (hX : IsClosedEmbedding (fun q : PuncturedPeriodTorus L => X q.1))
    (hhor : ∀ r : ℝ, (![r,0,0] : Fin 3 → ℝ) ∈ range (fun q : PuncturedPeriodTorus L => X q.1))
    (hver : ∀ r : ℝ, (![0,0,r] : Fin 3 → ℝ) ∈ range (fun q : PuncturedPeriodTorus L => X q.1))
    (hreg : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => X (periodTorusProjection L w) j) z) ∧
      ConformalCoordinateDerivatives (X ∘ periodTorusProjection L) z ∧ Function.Injective (fderiv ℝ (X ∘ periodTorusProjection L) z))
    (hh : meromorphicOrderAt (fun w => immersionComplexCoefficient (X ∘ periodTorusProjection L) w 2) 0 = (-2:ℤ))
    (hg : meromorphicOrderAt (immersionGaussLogDerivative (X ∘ periodTorusProjection L)) 0 = (-2:ℤ)) :
    ∃ W ∈ embeddedPitchFamily, (∃ s : ℂ, s ≠ 0 ∧ ∀ z : ℂ, z ∈ L.lattice ↔ s*z ∈ (rhombicPeriodPair W.t W.ht).lattice) ∧
      (spatialSimilaritySetoid _).r (range (fun q : PuncturedPeriodTorus L => coordinateToEuclidean (X q.1))) W.image := by
  obtain ⟨s,t,hs,ht,hp,hY⟩ := straight_axes_to_two_axis_harmonic_immersion L X hX hhor hver hreg
  let A := rhombicPeriodPair t ht
  obtain ⟨e,he⟩ := scaled_harmonic_quotient_correspondence L A s hs hp X hY
  have hi : Function.Injective (harmonicTorusImmersion hY) := by
    intro q r h
    obtain ⟨u,rfl⟩ := e.surjective q
    obtain ⟨v,rfl⟩ := e.surjective r
    exact congrArg e (hX.injective ((he u).symm.trans (h.trans (he v))))
  obtain ⟨h₁,h₂⟩ := marked_torus_scaled_end_orders L A (X ∘ periodTorusProjection L) s⁻¹ (inv_ne_zero hs)
    (fun z hz => ⟨(hreg z hz).1,(hreg z hz).2.1⟩) hh hg
  obtain ⟨W,hW,hWt,hS⟩ := original_embedded_harmonic_presents_in_pitch_family hw ht hY hi h₁ h₂
  have hr : range (coordinateToEuclidean ∘ harmonicTorusImmersion hY) =
      range (fun q : PuncturedPeriodTorus L => coordinateToEuclidean (X q.1)) := by
    rw [← e.surjective.range_comp (coordinateToEuclidean ∘ harmonicTorusImmersion hY)]
    apply congrArg range
    exact funext fun q => congrArg coordinateToEuclidean (he q)
  exact ⟨W,hW,⟨s,hs,by simpa only [hWt] using hp⟩,hr ▸ hS⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_embedded_pitch_normalization
