import TwoAxisHelicoid.ClosedLoopHeightStability
import TwoAxisHelicoid.RegularBoundaryManifold
import Mathlib.Analysis.Normed.Module.Connected

namespace TwoAxisHelicoid
open Set Metric Filter Topology
open scoped unitInterval Topology

/-- A regular height chart in the surface gives a real chart on the
level subspace, even when other components of that level are singular. -/
theorem chart_on_regular_height_slice {M : Type*} [TopologicalSpace M]
    {h : M → ℝ} {v : ℝ} (q : h ⁻¹' {v}) (e : OpenPartialHomeomorph M (ℝ×ℝ))
    (src : q.1∈e.source) (height : ∀ w∈e.target, h (e.symm w)=w.2) :
    ∃ a : OpenPartialHomeomorph (h ⁻¹' {v}) ℝ, q∈a.source := by
  let T : (ℝ×ℝ) ≃ₜ (ℝ×ℝ) := {
    toFun := fun w => (w.2-v,w.1)
    invFun := fun w => (w.2,w.1+v)
    left_inv := fun w => Prod.ext rfl (sub_add_cancel _ _)
    right_inv := fun w => Prod.ext (add_sub_cancel_right _ _) rfl
    continuous_toFun := (continuous_snd.sub continuous_const).prodMk continuous_fst
    continuous_invFun := continuous_snd.prodMk (continuous_fst.add continuous_const) }
  let d := e.trans T.toOpenPartialHomeomorph
  have qs : q.1∈d.source := ⟨src,mem_univ _⟩
  have line : d.IsImage (h ⁻¹' {v}) ({0} ×ˢ (univ : Set ℝ)) := by
    intro y hy
    have eq := height (e y) (e.map_source hy.1)
    rw [e.left_inv hy.1] at eq
    change ((e y).2-v=0 ∧ (e y).1∈(univ : Set ℝ)) ↔ h y=v
    rw [eq,sub_eq_zero]
    simp
  obtain ⟨a,srca,_⟩ := line_chart_on_slice q d qs line
  exact ⟨a,srca⟩

/-- A component on which each point has a real chart in the ambient
fiber is open and is locally path connected with its own topology. -/
theorem regular_component_locally_path_connected {S : Type*} [TopologicalSpace S] (x : S)
    (charts : ∀ y∈connectedComponent x, ∃ e : OpenPartialHomeomorph S ℝ, y∈e.source) :
    IsOpen (connectedComponent x) ∧ LocallyPathConnectedSpace (connectedComponent x) := by
  classical
  have op : IsOpen (connectedComponent x) := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    obtain ⟨e,src⟩ := charts y hy
    obtain ⟨r,rp,inside⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds (e.map_source src))
    let V := ball (e y) r
    have connected : IsPreconnected (e.symm '' V) := isPreconnected_ball.image e.symm (e.continuousOn_symm.mono inside)
    have sub : e.symm '' V⊆connectedComponent y := connected.subset_connectedComponent
      ⟨e y,Metric.mem_ball_self rp,e.left_inv src⟩
    rw [connectedComponent_eq hy]
    have nb := e.symm.image_mem_nhds (e.map_source src) (Metric.ball_mem_nhds (e y) rp)
    rw [e.left_inv src] at nb
    exact Filter.mem_of_superset nb sub
  let U : TopologicalSpace.Opens S := ⟨connectedComponent x,op⟩
  have nonempty : Nonempty U := ⟨⟨x,mem_connectedComponent⟩⟩
  choose chart point using fun y : U => charts y.1 y.2
  let c := fun y : U => (chart y).subtypeRestr (s:=U) nonempty
  have csrc (y : U) : y∈(c y).source := by
    change y∈((chart y).subtypeRestr _).source
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact point y
  let : ChartedSpace ℝ U := ⟨range c,c,csrc,mem_range_self⟩
  exact ⟨op,ChartedSpace.locallyPathConnectedSpace ℝ U⟩

/-- An obstructing component consisting of regular chart points has
obstructing components at every sufficiently close height. This
includes the level of a topologically regular filled-in cap point. -/
theorem regular_component_height_obstruction_persists {M : Type*} [TopologicalSpace M]
    (H : C(M,Circle×Circle)) (h : M → ℝ) (v : ℝ) (x : h ⁻¹' {v})
    (charts : ∀ y∈connectedComponent x, ∃ e : OpenPartialHomeomorph M (ℝ×ℝ),
      y.1∈e.source ∧ ∀ w∈e.target, h (e.symm w)=w.2)
    (obstruct : ¬∃ a b : C(connectedComponent x,ℝ), ∀ q : connectedComponent x,
      normalizedPhase (a q)=(H q.1.1).1 ∧ normalizedPhase (b q)=(H q.1.1).2) :
    ∀ᶠ s in 𝓝 v, ∃ q : h ⁻¹' {s}, ¬∃ a b : C(connectedComponent q,ℝ), ∀ z : connectedComponent q,
      normalizedPhase (a z)=(H z.1.1).1 ∧ normalizedPhase (b z)=(H z.1.1).2 := by
  let D := connectedComponent x
  have fiberChart (q : h ⁻¹' {v}) (hq : q∈D) : ∃ e : OpenPartialHomeomorph (h ⁻¹' {v}) ℝ, q∈e.source := by
    obtain ⟨e,src,height⟩ := charts q hq
    exact chart_on_regular_height_slice q e src height
  let : LocallyPathConnectedSpace D := (regular_component_locally_path_connected x fiberChart).2
  let : ConnectedSpace D := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  let : PathConnectedSpace D := PathConnectedSpace.of_locallyPathConnectedSpace
  let incl : C(D,M) := ⟨fun q => q.1.1,continuous_subtype_val.comp continuous_subtype_val⟩
  let q₀ : D := ⟨x,mem_connectedComponent⟩
  obtain ⟨γ,obs⟩ := nonlifting_phase_pair_detected_by_loop (H.comp incl) q₀ obstruct
  apply regular_loop_height_obstruction_persists H h v (γ.map incl.continuous)
  · exact fun t => (γ t).1.2
  · exact fun t => charts (γ t).1 (γ t).2
  · exact obs

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.regular_component_height_obstruction_persists
