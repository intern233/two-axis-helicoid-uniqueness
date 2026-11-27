import TwoAxisHelicoid.OriginalPoleEndTorusReduction

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace
open scoped Topology ContDiff Manifold

universe u

/-- Uniformization after a holomorphic filling gives harmonic torus
coordinates on the original finite surface without either pole formula. -/
theorem marked_harmonic_torus_of_filling {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {L₀ : PeriodPair}
    (top : M ≃ₜ PuncturedPeriodTorus L₀) (uniform : CompactGenusOneUniformization.{u} L₀)
    (X : M → Fin 3 → ℝ) (closed : IsClosedEmbedding X) (charts : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e)
    (E : PuncturedComplexEnd M) (hol : E.coord∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) :
    ∃ (L : PeriodPair) (f : M ≃ₜ PuncturedPeriodTorus L) (Y : PeriodTorus L → Fin 3 → ℝ),
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f.symm ∧
      (∀ x, Y (f x).1=X x) ∧ IsClosedEmbedding (fun q : PuncturedPeriodTorus L => Y q.1) ∧
      range (fun q : PuncturedPeriodTorus L => Y q.1)=range X ∧
      ∀ z∉L.lattice, (∀ j, HarmonicAt (fun w => Y (periodTorusProjection L w) j) z) ∧
        ConformalCoordinateDerivatives (Y ∘ periodTorusProjection L) z ∧ Function.Injective (fderiv ℝ (Y ∘ periodTorusProjection L) z) := by
  have hlc : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ℂ M
  let _ := compactifiedEndAtlas E
  have hman := compactifiedEndAtlas_isManifold E hol
  have hcm : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint M) := hman
  have ht : OnePoint M ≃ₜ PeriodTorus L₀ := top.onePointCongr.trans (punctureCompactification (0:PeriodTorus L₀))
  obtain ⟨L,H,h0,hH,hi,hf,hir⟩ := compactified_uniformization_restricts E (uniform (OnePoint M) ⟨ht⟩)
  let f := markedPuncturedUniformization H h0
  let Z := fun q : OnePoint M => q.elim (0 : Fin 3 → ℝ) X
  let Y := Z ∘ H.symm
  have hfin (x : M) : Y (f x).1=X x := by
    change (H.symm (H (x:OnePoint M))).elim _ X=X x
    rw [H.symm_apply_apply]
    rfl
  obtain ⟨hc,im⟩ := marked_immersion_closedEmbedding_range H h0 X closed 0
  exact ⟨L,f,Y,hf,hir,hfin,hc,im,marked_harmonic_immersion_coordinates E X 0 charts hman H h0 hH hi⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_harmonic_torus_of_filling
