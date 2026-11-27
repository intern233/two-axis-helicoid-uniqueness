import TwoAxisHelicoid.MarkedTorusCertifiedRigidity
import TwoAxisHelicoid.ConformalTorusScaling
import TwoAxisHelicoid.HarmonicAxisIntersectionPoint

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace
open scoped Topology ContDiff Manifold

/-- The comparison with the certified model extends to a biholomorphism
of the compactifications taking puncture to puncture. -/
theorem marked_straight_axes_biholomorphic_to_certified (hHW : RhombicHelicoidIntersectionPrinciple)
    (L : PeriodPair) (X : PeriodTorus L → Fin 3 → ℝ)
    (hX : IsClosedEmbedding (fun q : PuncturedPeriodTorus L => X q.1))
    (hhor : ∀ r : ℝ, (![r,0,0] : Fin 3 → ℝ) ∈ range (fun q : PuncturedPeriodTorus L => X q.1))
    (hver : ∀ r : ℝ, (![0,0,r] : Fin 3 → ℝ) ∈ range (fun q : PuncturedPeriodTorus L => X q.1))
    (hhi : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => X (periodTorusProjection L w) j) z) ∧
      ConformalCoordinateDerivatives (X ∘ periodTorusProjection L) z ∧
      Function.Injective (fderiv ℝ (X ∘ periodTorusProjection L) z))
    (hheight : meromorphicOrderAt (fun z => immersionComplexCoefficient (X ∘ periodTorusProjection L) z 2) 0 = (-2:ℤ))
    (hgauss : meromorphicOrderAt (immersionGaussLogDerivative (X ∘ periodTorusProjection L)) 0 = (-2:ℤ)) :
    ∃ (B : PeriodTorus L ≃ₜ PeriodTorus certifiedPeriodPair) (U : PuncturedPeriodTorus L ≃ₜ PuncturedPeriodTorus certifiedPeriodPair)
      (k : ℝ) (E : EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3)) (b : EuclideanSpace ℝ (Fin 3)),
      B 0 = 0 ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω B ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω B.symm ∧
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω U ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω U.symm ∧
      (∀ q, (U q).1 = B q.1) ∧ X (U.symm (rhombicAxisPoint certifiedClosedParameters.height_pos)).1 = 0 ∧ 0 < k ∧
      ∀ q, certifiedTorusImmersion (U q) = k • E (coordinateToEuclidean (X q.1))+b := by
  obtain ⟨s,t,hs,ht,hp,hY⟩ := straight_axes_to_two_axis_harmonic_immersion L X hX hhor hver hhi
  let M := rhombicPeriodPair t ht
  obtain ⟨B,e,hzero,hB,hI,hf,hfi,hBE,he⟩ := scaled_harmonic_biholomorphic_correspondence L M s hs hp X hY
  have hi : Function.Injective (harmonicTorusImmersion hY) := by
    intro q r h
    obtain ⟨u,rfl⟩ := e.surjective q
    obtain ⟨v,rfl⟩ := e.surjective r
    exact congrArg e (hX.injective ((he u).symm.trans (h.trans (he v))))
  obtain ⟨hh,hg⟩ := marked_torus_scaled_end_orders L M (X ∘ periodTorusProjection L) s⁻¹
    (inv_ne_zero hs) (fun z hz => ⟨(hhi z hz).1,(hhi z hz).2.1⟩) hheight hgauss
  obtain ⟨ht',k,E,b,hk,hpoint⟩ := harmonic_meromorphic_similarity_to_certified_cover hHW ht hY hi hh hg
  subst t
  have hc := (he (e.symm (rhombicAxisPoint certifiedClosedParameters.height_pos))).symm
  rw [e.apply_symm_apply,harmonicTorus_axis_point _ hY] at hc
  refine ⟨B,e,k,E,b,hzero,hB,hI,hf,hfi,hBE,hc,hk,?_⟩
  have point (q : PuncturedPeriodTorus certifiedPeriodPair) :
      certifiedTorusImmersion q = k • E (coordinateToEuclidean (harmonicTorusImmersion hY q))+b := by
    obtain ⟨z,hz⟩ := Quotient.exists_rep q.1
    have hproj : periodTorusProjection certifiedPeriodPair z = q.1 := hz
    have hn : z ∉ certifiedPeriodPair.lattice :=
      fun h => q.2 (hproj.symm.trans ((periodTorusProjection_eq_zero _ z).mpr h))
    let r : PuncturedPeriodTorus certifiedPeriodPair :=
      ⟨periodTorusProjection certifiedPeriodPair z,fun h => hn ((periodTorusProjection_eq_zero _ z).mp h)⟩
    have hr : r = q := Subtype.ext hproj
    have hYr : harmonicTorusImmersion hY r = X (periodTorusProjection L (s⁻¹*z)) :=
      harmonicTorusImmersion_projection hY hn
    rw [← hr,hYr]
    exact hpoint z hn
  intro q
  exact (point (e q)).trans (by rw [he])

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.marked_straight_axes_biholomorphic_to_certified
