import TwoAxisHelicoid.PositionalDistanceNormalTube
import TwoAxisHelicoid.GeneralThinTubeLemma
import TwoAxisHelicoid.ExteriorHeightEscape

namespace TwoAxisHelicoid
open Complex Filter Set Topology
open scoped Topology ContDiff Manifold

/-- In the physical reference frame this measures the ordinary
Weingarten derivative with the induced Euclidean metric on tangent
vectors, uniformly off a compact subset of the original surface. -/
def HasBoundedPhysicalEndCurvature (s : OriginalSmoothHelicoid) : Prop :=
  let X := centeredHelicoidNormalization s.axes.pitch_ne ∘ s.position
  ∃ (K : Set s.carrier) (B : ℝ), IsCompact K ∧ 0≤B ∧ ∀ q∉K, ∀ v : ℂ,
    ‖fderiv ℝ (euclideanUnitChartNormal (X ∘ (chartAt ℂ q).symm)) ((chartAt ℂ q) q) v‖ ≤
      B*‖coordinateToEuclidean (fderiv ℝ (X ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q) v)‖

/-- One-sided spatial C⁰ convergence of an original embedded surface,
plus a curvature bound on its end, suffices for the actual global C¹
normal graph on that end. No conformal end data are used. -/
theorem positional_c1_graph_of_bounded_shape (s : OriginalPositionallyAsymptoticHelicoid)
    (bounded : HasBoundedPhysicalEndCurvature s.toOriginalSmoothHelicoid) :
    HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization s.axes.pitch_ne ![0,0,0] ∘ s.position) := by
  let A := centeredHelicoidNormalization s.axes.pitch_ne
  let X := A ∘ s.position
  have hz : (![0,0,0] : Fin 3 → ℝ)=0 := by ext j; fin_cases j <;> rfl
  rw [hz]
  change HasHelicoidC1End (coordinateToTube ∘ X)
  have cl : IsClosedEmbedding X := A.toHomeomorph.isClosedEmbedding.comp s.closedEmbedding
  have sm : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X := A.toContinuousLinearMap.contMDiff.comp s.smooth
  have inj (q : s.carrier) : Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X q) := by
    have sa : ContMDiff 𝓘(ℝ,Fin 3 → ℝ) 𝓘(ℝ,Fin 3 → ℝ) ∞ A.toContinuousLinearMap := A.toContinuousLinearMap.contMDiff
    change Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) (A.toContinuousLinearMap ∘ s.position) q)
    rw [mfderiv_comp q
      (sa.mdifferentiable (by simp) _) (s.smooth.mdifferentiable (by simp) _),
      mfderiv_eq_fderiv,A.toContinuousLinearMap.hasFDerivAt.fderiv]
    exact A.injective.comp (s.immersion q)
  have nont := punctured_complex_curve_noncompact (0:PeriodTorus s.modelTorus)
  have non : NoncompactSpace s.carrier := ⟨fun h => noncompact_univ (PuncturedPeriodTorus s.modelTorus) (by
    simpa only [image_univ,s.topologicalType.surjective.range_eq] using h.image s.topologicalType.continuous)⟩
  have tails := homeomorphic_punctured_surface_connected_tails (0:PeriodTorus s.modelTorus) s.topologicalType
  have connected (K : Set s.carrier) (hK : IsCompact K) : ∃ U : Set s.carrier, IsConnected U ∧ IsCompact Uᶜ ∧ Disjoint U K := by
    obtain ⟨U,conn,k,d⟩ := tails K hK
    have ne : U.Nonempty := by
      by_contra h
      have empty := not_nonempty_iff_eq_empty.mp h
      rw [empty,compl_empty] at k
      exact noncompact_univ s.carrier k
    exact ⟨U,⟨ne,conn⟩,k,d⟩
  obtain ⟨K,B,k,bpos,shape⟩ := bounded
  exact general_thin_tube_lemma_4_3 X cl.isProperMap cl.injective sm inj connected k bpos shape
    (positional_standard_end_actual_tubes cl.isProperMap (reference_frame_positional_standard _ s.axes.pitch_ne s.approaches))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positional_c1_graph_of_bounded_shape
