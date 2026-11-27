import TwoAxisHelicoid.ComplexEndCompactification
import Mathlib.Geometry.Manifold.LocalDiffeomorph

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Manifold Topology ContDiff

variable {E M : Type*} [TopologicalSpace E] [TopologicalSpace M] [ChartedSpace ℂ M]
variable {p : E → M} (hp : IsLocalHomeomorph p)

/-- The Riemann surface atlas pulled back from the base of a topological
covering. A lifted local coordinate is a covering sheet followed by a
base coordinate. -/
@[instance_reducible] noncomputable def holomorphicCoverAtlas : ChartedSpace ℂ E where
  atlas := {e | ∃ (d : OpenPartialHomeomorph E M) (c : OpenPartialHomeomorph M ℂ),
    p = d ∧ c ∈ atlas ℂ M ∧ e = d.trans c}
  chartAt x := (hp x).choose.trans (chartAt ℂ (p x))
  mem_chart_source x := ⟨(hp x).choose_spec.1,
    (congrFun (hp x).choose_spec.2 x) ▸ mem_chart_source ℂ (p x)⟩
  chart_mem_atlas x := ⟨_,_,(hp x).choose_spec.2,chart_mem_atlas ℂ (p x),rfl⟩

theorem holomorphicCoverAtlas_isManifold [IsManifold 𝓘(ℂ,ℂ) ω M] :
    let _ := holomorphicCoverAtlas hp; IsManifold 𝓘(ℂ,ℂ) ω E := by
  let _ := holomorphicCoverAtlas hp
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨d,c,hd,hc,rfl⟩ ⟨d',c',hd',hc',rfl⟩ z hz
  let e := d.trans c
  let e' := d'.trans c'
  have hsrc : z ∈ (e.symm.trans e').source := hz.1
  have heq (w : ℂ) (hw : w ∈ (e.symm.trans e').source) : d' (d.symm (c.symm w)) = c.symm w := by
    rw [← congrFun hd' _,congrFun hd _,d.right_inv hw.1.2]
  have hz' : z ∈ (c.symm.trans c').source := ⟨hsrc.1.1,by
    change c.symm z ∈ c'.source
    rw [← heq z hsrc]; exact hsrc.2.2⟩
  change ContDiffWithinAt ℂ ω (e.symm.trans e') _ z
  apply ContDiffAt.contDiffWithinAt
  apply (complexAtlas_realized_transition (IsManifold.subset_maximalAtlas hc)
    (IsManifold.subset_maximalAtlas hc') hz').congr_of_eventuallyEq
  filter_upwards [(e.symm.trans e').open_source.mem_nhds hsrc] with w hw
  exact congrArg c' (heq w hw)

theorem holomorphicCoverAtlas_localDiffeomorph [IsManifold 𝓘(ℂ,ℂ) ω M] :
    let _ := holomorphicCoverAtlas hp
    IsLocalDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω p := by
  let _ := holomorphicCoverAtlas hp
  have hm : IsManifold 𝓘(ℂ,ℂ) ω E := holomorphicCoverAtlas_isManifold hp
  change IsLocalDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω p
  intro x
  obtain ⟨d,hx,he⟩ := hp x
  have hc (c : OpenPartialHomeomorph M ℂ) (hcp : c ∈ atlas ℂ M) :
      d.trans c ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω E :=
    IsManifold.subset_maximalAtlas (show d.trans c ∈ atlas ℂ E from ⟨d,c,he,hcp,rfl⟩)
  let D : PartialDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) E M ω := {
    toPartialEquiv := d.toPartialEquiv
    open_source := d.open_source
    open_target := d.open_target
    contMDiffOn_toFun := by
      intro y hy
      let c := chartAt ℂ (d y)
      have hyc : d y ∈ c.source := mem_chart_source ℂ (d y)
      have hy' : y ∈ (d.trans c).source := ⟨hy,hyc⟩
      have h₁ := contMDiffAt_of_mem_maximalAtlas (hc c (chart_mem_atlas ℂ (d y))) hy'
      have h₂ := contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℂ,ℂ)) (n := ω)
        (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ (d y))) (c.map_source hyc)
      apply ContMDiffAt.contMDiffWithinAt
      apply (h₂.comp y h₁).congr_of_eventuallyEq
      filter_upwards [(d.trans c).open_source.mem_nhds hy'] with w hw
      exact (c.left_inv hw.2).symm
    contMDiffOn_invFun := by
      intro y hy
      let c := chartAt ℂ y
      have hyc : y ∈ c.source := mem_chart_source ℂ y
      have hy' : c y ∈ (d.trans c).target := ⟨c.map_source hyc,by change c.symm (c y) ∈ d.target; rwa [c.left_inv hyc]⟩
      have h₁ := contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℂ,ℂ)) (n := ω)
        (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ y)) hyc
      have h₂ := contMDiffAt_symm_of_mem_maximalAtlas (hc c (chart_mem_atlas ℂ y)) hy'
      apply ContMDiffAt.contMDiffWithinAt
      apply (h₂.comp y h₁).congr_of_eventuallyEq
      filter_upwards [c.open_source.mem_nhds hyc] with w hw
      exact congrArg d.symm (c.left_inv hw).symm }
  exact ⟨D,hx,fun y _ => congrFun he y⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.holomorphicCoverAtlas_isManifold
#print axioms TwoAxisHelicoid.holomorphicCoverAtlas_localDiffeomorph
