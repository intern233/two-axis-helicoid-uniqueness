import TwoAxisHelicoid.ComplexEndCompactification
import TwoAxisHelicoid.PointedTorusUniformization

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology OnePoint ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M]

/-- The inverse of the original inclusion, where defined, has the identity
as its coordinate expression in the filled atlas. -/
theorem compactifiedEnd_finite_inverse_contMDiffAt (E : PuncturedComplexEnd M) (b x : M) :
    let _ := compactifiedEndAtlas E
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun p : OnePoint M => p.elim b id) (x:OnePoint M) := by
  let _ := compactifiedEndAtlas E
  let e := chartAt ℂ x
  apply contMDiffAt_iff.mpr
  refine ⟨OnePoint.continuousAt_coe.mpr (show ContinuousAt id x from continuousAt_id),?_⟩
  have he : (fun z => e (e.symm z)) =ᶠ[𝓝 (e x)] id := by
    filter_upwards [e.open_target.mem_nhds (e.map_source (mem_chart_source ℂ x))] with z hz
    exact e.right_inv hz
  exact ((contDiffAt_id (𝕜 := ℂ) (n := ω)).congr_of_eventuallyEq he).contDiffWithinAt

/-- Remove the marked points from an actual homeomorphism of the two
compactifications. Its finite map is the original map followed by inclusion. -/
noncomputable def markedPuncturedUniformization {L : PeriodPair}
    (H : OnePoint M ≃ₜ PeriodTorus L) (h0 : H OnePoint.infty = 0) : M ≃ₜ PuncturedPeriodTorus L := by
  let Y := fun x : M => H (x:OnePoint M)
  have hi : IsEmbedding Y := H.isEmbedding.comp OnePoint.isOpenEmbedding_coe.isEmbedding
  have hn (x : M) : Y x ≠ 0 := fun hx => OnePoint.coe_ne_infty x (H.injective (hx.trans h0.symm))
  apply (hi.codRestrict _ hn).toHomeomorphOfSurjective
  intro q
  have hq : H.symm q.1 ≠ OnePoint.infty := by
    intro hh
    apply q.2
    rw [← H.apply_symm_apply q.1,hh,h0]
  obtain ⟨x,hx⟩ := OnePoint.ne_infty_iff_exists.mp hq
  exact ⟨x,Subtype.ext ((congrArg H hx).trans (H.apply_symm_apply _))⟩

omit [T2Space M] [ChartedSpace ℂ M] in
theorem markedPuncturedUniformization_coe {L : PeriodPair}
    (H : OnePoint M ≃ₜ PeriodTorus L) (h0 : H OnePoint.infty = 0) (x : M) :
    (markedPuncturedUniformization H h0 x).1 = H (x : OnePoint M) := rfl

/-- With only the unmarked uniformization input, one obtains the actual
punctured-torus biholomorphism on the original open surface and a pointed
biholomorphic extension to its compactification. -/
theorem compactified_uniformization_restricts [IsManifold 𝓘(ℂ,ℂ) ω M] (E : PuncturedComplexEnd M)
    (hm : let _ := compactifiedEndAtlas E; AdmitsPeriodTorusUniformization (OnePoint M)) :
    let _ := compactifiedEndAtlas E
    ∃ (L : PeriodPair) (H : OnePoint M ≃ₜ PeriodTorus L) (h0 : H OnePoint.infty = 0),
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H.symm ∧
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (markedPuncturedUniformization H h0) ∧
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (markedPuncturedUniformization H h0).symm := by
  let _ := compactifiedEndAtlas E
  obtain ⟨L,H,h0,hH,hi⟩ := compact_uniformization_mark_point hm OnePoint.infty
  let f := markedPuncturedUniformization H h0
  refine ⟨L,H,h0,hH,hi,?_,?_⟩
  · intro x
    have hh : ContMDiffWithinAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (Subtype.val ∘ f) univ x :=
      (hH.comp (compactifiedEnd_inclusion_contMDiff E)).contMDiffAt.contMDiffWithinAt
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff (U := puncturedPeriodTorusOpen L) f univ x).mp hh
  · intro q
    let x := f.symm q
    let g := fun r : PuncturedPeriodTorus L => H.symm r.1
    have hg : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω g := hi.comp (contMDiff_subtype_val (U := puncturedPeriodTorusOpen L))
    have hx (r : PuncturedPeriodTorus L) : g r = (f.symm r : OnePoint M) := by
      apply H.injective
      change H (H.symm r.1) = H (f.symm r:OnePoint M)
      rw [H.apply_symm_apply,← markedPuncturedUniformization_coe H h0]
      exact congrArg Subtype.val (f.apply_symm_apply r).symm
    have hn : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun p : OnePoint M => p.elim x id) (g q) := by
      rw [hx q]
      exact compactifiedEnd_finite_inverse_contMDiffAt E x _
    apply (hn.comp q hg.contMDiffAt).congr_of_eventuallyEq
    exact Eventually.of_forall fun r => by
      change f.symm r = (g r).elim x id
      rw [hx r]
      rfl

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compactified_uniformization_restricts
