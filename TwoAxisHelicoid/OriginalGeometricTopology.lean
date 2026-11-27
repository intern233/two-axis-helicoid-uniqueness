import TwoAxisHelicoid.ActualTorusManifoldImmersion
import TwoAxisHelicoid.OriginalHandleTopology
import TwoAxisHelicoid.ComplexPunctureTail
import TwoAxisHelicoid.PuncturedCurveNoncompact
import TwoAxisHelicoid.CompactPunctureHomeomorphism
import Mathlib.Analysis.Convex.Contractible

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology OnePoint

/-- No topological plane embedding can have exactly the given physical
image. This follows from the nontrivial handle before any asymptotic or
analytic theorem is used. -/
theorem OriginalSmoothHelicoid.image_ne_embedded_plane (s : OriginalSmoothHelicoid)
    (P : ℂ → Fin 3 → ℝ) (he : IsEmbedding P) : range s.position ≠ range P := by
  intro h
  let f := (s.closedEmbedding.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr h)).trans he.toHomeomorph.symm
  exact s.not_simply_connected (f.toHomotopyEquiv.simplyConnectedSpace_iff.mpr inferInstance)

/-- The one-point compactification is already the topological torus and its
new point is exactly the missing origin, before any complex structure has
been constructed on the compactification. -/
noncomputable def OriginalSmoothHelicoid.topologicalCompactification (s : OriginalSmoothHelicoid) :
    OnePoint s.carrier ≃ₜ PeriodTorus s.modelTorus :=
  s.topologicalType.onePointCongr.trans (punctureCompactification (0 : PeriodTorus s.modelTorus))

theorem OriginalSmoothHelicoid.topologicalCompactification_end (s : OriginalSmoothHelicoid) :
    s.topologicalCompactification ∞ = 0 := rfl

/-- Connected open subends with compact complements form a cofinal system
on the original surface. This is the uniqueness of its topological end in
the compact-exhaustion formulation used by the exterior theorem. -/
theorem OriginalSmoothHelicoid.one_topological_end (s : OriginalSmoothHelicoid)
    (K : Set s.carrier) (hK : IsCompact K) :
    ∃ U : Set s.carrier, IsOpen U ∧ IsConnected U ∧ IsCompact Uᶜ ∧ Disjoint U K := by
  let f := s.topologicalType
  obtain ⟨V,hVo,hVc,hVk,hVd⟩ := compact_complex_puncture_connected_tail
    (0 : PeriodTorus s.modelTorus) (hK.image f.continuous)
  have hne := cofinite_punctured_curve_nonempty (0 : PeriodTorus s.modelTorus) hVk
  refine ⟨f ⁻¹' V,hVo.preimage f.continuous,f.isConnected_preimage.mpr ⟨hne,hVc⟩,?_,?_⟩
  · exact f.isCompact_preimage.mpr hVk
  · apply Set.disjoint_left.mpr
    intro x hx hk
    exact Set.disjoint_left.mp hVd hx ⟨x,hk,rfl⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.OriginalSmoothHelicoid.image_ne_embedded_plane
#print axioms TwoAxisHelicoid.OriginalSmoothHelicoid.one_topological_end
