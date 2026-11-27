import TwoAxisHelicoid.SpatialSheetInverseGerms
import TwoAxisHelicoid.LocalDerivativeCoreTransport

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology ContDiff Manifold

/-- A continuous open marking of a whole core in the moving punctured
torus is C¹ whenever its actual Euclidean position is C¹ in the
covering plane. This statement applies to the marking supplied by the
physical normal projection, without choosing a smooth inverse to it. -/
theorem smooth_torus_core_of_plane_position {A : PeriodPair} (C : TorusGeneratingCoreModel A)
    (W : PitchNormalizedBasicImmersion) (member : W∈embeddedPitchFamily)
    (σ : C.carrier → PuncturedPeriodTorus (rhombicPeriodPair W.t W.ht)) (embed : IsOpenEmbedding σ)
    (Z : ℂ → EuclideanSpace ℝ (Fin 3)) (smooth : ∀ z, periodTorusProjection A z∈C.carrier → ContDiffAt ℝ 1 Z z)
    (space : ∀ (q : C.carrier) z, q.1=periodTorusProjection A z → W.torusPosition (σ q).1=Z z) :
    ∃ F : SmoothOpenTorusCoreMap C (rhombicPeriodPair W.t W.ht), ∀ q : C.carrier, F.map q.1=(σ q).1 := by
  classical
  let L := rhombicPeriodPair W.t W.ht
  let j := (Subtype.val : PuncturedPeriodTorus L → PeriodTorus L) ∘ σ
  let f := Function.extend (Subtype.val : C.carrier → PeriodTorus A) j (fun _ => 0)
  have agrees (q : C.carrier) : f q.1=j q := Subtype.val_injective.extend_apply ..
  have oncore : (fun q : C.carrier => f q.1)=j := funext agrees
  refine ⟨⟨f,?_,?_,fun x hx => (agrees ⟨x,hx⟩) ▸ (σ ⟨x,hx⟩).2⟩,agrees⟩
  · rw [oncore]
    exact isOpen_ne.isOpenEmbedding_subtypeVal.comp embed
  · intro x hx
    let q : C.carrier := ⟨x,hx⟩
    let a := chartAt ℂ x
    have ax : x∈a.source := mem_chart_source ℂ x
    have inv (y : PeriodTorus A) (hy : y∈a.source) : periodTorusProjection A (a y)=y := by
      rw [← periodTorus_chart_symm_eq_projection A x]
      exact a.left_inv hy
    let S := Z ∘ a
    have sm : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,EuclideanSpace ℝ (Fin 3)) 1 S x :=
      (contMDiffAt_iff_contDiffAt.mpr (smooth _ ((inv x ax).symm ▸ hx))).comp x
        (contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ x)) ax)
    have actual : ∀ᶠ y in 𝓝 q, S y.1=W.torusPosition (σ y).1 := by
      filter_upwards [continuous_subtype_val.continuousAt (a.open_source.mem_nhds ax)] with y hy
      exact (space y (a y.1) (inv _ hy).symm).symm
    obtain ⟨g,hg,eq⟩ := torus_sheet_inverse_germ_of_spatial_section C W member q σ embed.continuous.continuousAt S sm actual
    have germ : f=ᶠ[𝓝 x] g := by
      rw [← C.isOpen_carrier.isOpenEmbedding_subtypeVal.map_nhds_eq (x := q)]
      exact eq.mono (fun y hy => (agrees y).trans hy.symm)
    exact (hg.congr_of_eventuallyEq germ).contMDiffWithinAt

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_torus_core_of_plane_position
