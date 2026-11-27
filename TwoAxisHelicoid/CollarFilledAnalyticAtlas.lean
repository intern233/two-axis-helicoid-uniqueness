import TwoAxisHelicoid.PunctureOuterCollar

namespace TwoAxisHelicoid
open Set Metric Filter Topology
open scoped Topology ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M]

/-- Use the old analytic charts on the core and the new disk coordinate
across infinity. Only their common collar must be holomorphic. -/
@[instance_reducible] noncomputable def collarFilledAtlas (E : PuncturedComplexEnd M)
    (U : Set M) (op : IsOpen U) (cover : ∀ x : M, x∈U ∨ x∈E.coord.source)
    [IsManifold 𝓘(ℂ,ℂ) ω M] : ChartedSpace ℂ (OnePoint M) := by
  classical
  let chart := fun x : M => (chartAt ℂ x).restr U
  have inside (x : M) : (chart x).source ⊆ U := by
    simpa only [chart,OpenPartialHomeomorph.restr_source,op.interior_eq] using (inter_subset_right (s:=(chartAt ℂ x).source) (t:=U))
  have good (x : M) : chart x∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M :=
    restr_mem_maximalAtlas (contDiffGroupoid ω 𝓘(ℂ,ℂ)) (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ x)) op
  exact {
    atlas := {d | (∃ e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M, e.source⊆U ∧ d=finiteOnePointChart e) ∨ d=E.filledChart}
    chartAt := OnePoint.rec E.filledChart (fun x => if x∈U then finiteOnePointChart (chart x) else E.filledChart)
    mem_chart_source := by
      intro p
      cases p using OnePoint.rec with
      | infty => exact OnePoint.infty_notMem_image_coe
      | coe x =>
        change (x:OnePoint M)∈(if x∈U then finiteOnePointChart (chart x) else E.filledChart).source
        by_cases hx : x∈U
        · rw [ite_eq_left hx,finiteOnePointChart_coe_source]
          exact (chartAt ℂ x).restr_source' U op ▸ ⟨mem_chart_source ℂ x,hx⟩
        · rw [ite_eq_right hx,compactifiedEndChart_coe_source]
          exact (cover x).resolve_left hx
    chart_mem_atlas := by
      intro p
      cases p using OnePoint.rec with
      | infty => exact Or.inr rfl
      | coe x =>
        by_cases hx : x∈U
        · exact Or.inl ⟨chart x,good x,inside x,ite_eq_left hx⟩
        · exact Or.inr (ite_eq_right hx) }

theorem collarFilledAtlas_isManifold [IsManifold 𝓘(ℂ,ℂ) ω M] (E : PuncturedComplexEnd M)
    (U : Set M) (op : IsOpen U) (cover : ∀ x : M, x∈U ∨ x∈E.coord.source)
    (c : OpenPartialHomeomorph M ℂ) (hol : c∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
    (src : E.coord.source=c.source) (same : ∀ x∈U, x∈E.coord.source → E.coord x=c x) :
    let _ := collarFilledAtlas E U op cover
    IsManifold 𝓘(ℂ,ℂ) ω (OnePoint M) := by
  let _ := collarFilledAtlas E U op cover
  have inverse {w : ℂ} (dw : w∈E.coord.target) (inU : E.coord.symm w∈U) :
      w∈c.target ∧ E.coord.symm w=c.symm w := by
    have source := E.coord.map_target dw
    have eqn := (same _ inU source).symm.trans (E.coord.right_inv dw)
    have dc : E.coord.symm w∈c.source := src ▸ source
    exact ⟨eqn ▸ c.map_source dc,(c.left_inv dc).symm.trans (congrArg c.symm eqn)⟩
  apply isManifold_of_contDiffOn
  intro e d he hd z hz
  have dom : z∈(e.symm.trans d).source := hz.1
  change ContDiffWithinAt ℂ ω (e.symm.trans d) _ z
  apply ContDiffAt.contDiffWithinAt
  rcases he with ⟨a,ha,au,rfl⟩|rfl <;> rcases hd with ⟨b,hb,bu,rfl⟩|rfl
  · have v := (finiteOnePointChart_coe_source b _).mp dom.2
    exact complexAtlas_realized_transition ha hb (show z∈(a.symm.trans b).source from ⟨dom.1,v⟩)
  · have member := (compactifiedEndChart_coe_source E _).mp dom.2
    have old : z∈(a.symm.trans c).source := ⟨dom.1,src ▸ member⟩
    apply (complexAtlas_realized_transition ha hol old).congr_of_eventuallyEq
    filter_upwards [(a.symm.trans c).open_source.mem_nhds old] with w hw
    exact same _ (au (a.map_target hw.1)) (src.symm ▸ hw.2)
  · have nz : z≠0 := by
      rintro rfl
      have bad : E.filledInverse 0 ∈ (finiteOnePointChart b).source := dom.2
      simp [PuncturedComplexEnd.filledInverse,finiteOnePointChart] at bad
    have disk : z∈E.coord.target := E.mem_target_of_ball_ne dom.1 nz
    have toB : E.coord.symm z∈b.source := by
      apply (finiteOnePointChart_coe_source b _).mp
      have h : E.filledInverse z∈(finiteOnePointChart b).source := dom.2
      simpa only [PuncturedComplexEnd.filledInverse,ite_eq_right nz] using h
    have back := inverse disk (bu toB)
    have bc : c.symm z∈b.source := back.2 ▸ toB
    have old : z∈(c.symm.trans b).source := ⟨back.1,bc⟩
    apply (complexAtlas_realized_transition hol hb old).congr_of_eventuallyEq
    have hit : z∈(E.coord.symm.trans b).source := ⟨disk,toB⟩
    filter_upwards [(E.coord.symm.trans b).open_source.mem_nhds hit,isOpen_compl_singleton.mem_nhds nz] with w hw nw
    change (E.filledInverse w).elim 0 b=b (c.symm w)
    rw [show E.filledInverse w=(E.coord.symm w : OnePoint M) by simp [PuncturedComplexEnd.filledInverse,show w≠0 from nw]]
    exact congrArg b (inverse hw.1 (bu hw.2)).2
  · apply (contDiffAt_id (𝕜:=ℂ) (n:=ω)).congr_of_eventuallyEq
    filter_upwards [E.filledChart.open_target.mem_nhds dom.1] with w hw
    exact E.filledChart.right_inv hw

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.collarFilledAtlas_isManifold

