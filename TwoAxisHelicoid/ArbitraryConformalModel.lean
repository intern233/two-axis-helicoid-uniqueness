import TwoAxisHelicoid.ConformalMarkedModel
import TwoAxisHelicoid.HorizontalLinePlacement

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace
open scoped Topology ContDiff Manifold

/-- The arbitrary horizontal axis is allowed in the pointed biholomorphic
comparison of compact tori as well as the pointwise spatial similarity. -/
theorem marked_arbitrary_axes_biholomorphic_to_certified
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
    ∃ (B : PeriodTorus L ≃ₜ PeriodTorus certifiedPeriodPair) (U : PuncturedPeriodTorus L ≃ₜ PuncturedPeriodTorus certifiedPeriodPair)
      (k : ℝ) (E : EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3)) (b : EuclideanSpace ℝ (Fin 3)),
      B 0 = 0 ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω B ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω B.symm ∧
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω U ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω U.symm ∧
      (∀ q, (U q).1 = B q.1) ∧ (∃ r : ℝ, A+r • ![c.re,c.im,0] = ![0,0,A 2]) ∧
      X (U.symm (rhombicAxisPoint certifiedClosedParameters.height_pos)).1 = ![0,0,A 2] ∧ 0 < k ∧
      ∀ q, certifiedTorusImmersion (U q) = k • E (coordinateToEuclidean (X q.1))+b := by
  let C : Fin 3 → ℝ := ![0,0,A 2]
  let R := lineAxisCoordinates c hc C
  obtain ⟨hlinecenter,hclosed,hhor,hvert,hregular,hh,hg⟩ :=
    horizontal_line_axes_placement L X hX c hc A hline hver hα hend hhi
  obtain ⟨B,U,k,E,b,h0,hB,hI,hU,hV,hBU,hcenter,hk,hpt⟩ :=
    marked_straight_axes_biholomorphic_to_certified hHW L (R ∘ X)
      hclosed hhor hvert hregular (hh.trans hheight) (hg.trans hgauss)
  have hcR : R C = 0 := by change verticalRotation _ (C-C) = 0; rw [sub_self,map_zero]
  have hx := R.injective (hcenter.trans hcR.symm)
  exact ⟨B,U,k,(euclideanOrientationIsometry R (lineAxisCoordinates_dist_sq c hc C)).trans E,
    b,h0,hB,hI,hU,hV,hBU,hlinecenter,hx,hk,hpt⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_arbitrary_axes_biholomorphic_to_certified
