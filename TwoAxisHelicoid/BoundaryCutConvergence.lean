import TwoAxisHelicoid.RegularBoundaryConnectedTails
import Mathlib.Topology.Order.IntermediateValue

namespace TwoAxisHelicoid
open Set Metric Filter Topology
open scoped Topology

/-- If arbitrarily small positive levels of a continuous parameter map
into arbitrarily small neighborhoods of one point, then the whole end
maps to that point. Connected interior sides exclude any second cluster
point; no regularity of the coordinate on the frontier is assumed. -/
theorem boundary_convergence_of_shrinking_cuts {D : Type*} [TopologicalSpace D]
    {W : Set ℂ} (compact : IsCompact (closure W)) (e : D ≃ₜ W) (g : D → ℝ)
    (cg : Continuous g) (pos : ∀ x, 0<g x)
    (sides : ∀ x∈closure W, ∀ G : Set ℂ, IsOpen G → x∈G →
      ∃ O : Set ℂ, IsOpen O ∧ x∈O ∧ O⊆G ∧ IsPreconnected (O∩W))
    {q : ℂ} (cuts : ∀ ε>0, ∀ δ>0, ∃ r : ℝ, 0<r ∧ r<δ ∧ ∀ x, g x=r → (e x).1∈ball q ε)
    {L : Filter D} (zero : Tendsto g L (𝓝 0)) : Tendsto (fun x => (e x).1) L (𝓝 q) := by
  apply compact.tendsto_nhds_of_unique_mapClusterPt (.of_forall fun x => subset_closure (e x).2)
  intro y cy cluster
  by_contra diff
  let ε := dist y q/3
  have ep : 0<ε := div_pos (dist_pos.mpr diff) (by norm_num)
  have miss : Disjoint (ball y ε) (ball q ε) := Metric.ball_disjoint_ball (by
    dsimp [ε]; linarith [dist_nonneg (x:=y) (y:=q)])
  obtain ⟨O,oo,yo,sub,connected⟩ := sides y cy _ isOpen_ball (mem_ball_self ep)
  obtain ⟨w,wo,ww⟩ := mem_closure_iff.mp cy O oo yo
  let a : W := ⟨w,ww⟩
  let P := (Subtype.val : W → ℂ) ⁻¹' O
  have conn : IsPreconnected P := Topology.IsInducing.subtypeVal.isPreconnected_image.mp (by
    rw [show (Subtype.val : W → ℂ) '' P=O∩W from (Subtype.image_preimage_coe W O).trans (inter_comm W O)]
    exact connected)
  obtain ⟨r,rp,larger,bounds⟩ := cuts ε ep _ (pos (e.symm a))
  have freq := mapClusterPt_iff_frequently.mp cluster O (oo.mem_nhds yo)
  obtain ⟨z,zo,small⟩ := (freq.and_eventually (zero.eventually (Iio_mem_nhds rp))).exists
  obtain ⟨u,up,value⟩ := conn.intermediate_value (show e z∈P from zo) (show a∈P from wo)
    (cg.comp e.symm.continuous).continuousOn (show r∈Icc ((g ∘ e.symm) (e z)) ((g ∘ e.symm) a) by
      simpa only [mem_Icc,Function.comp_apply,e.symm_apply_apply] using And.intro small.le larger.le)
  have hit := bounds (e.symm u) value
  rw [e.apply_symm_apply] at hit
  exact disjoint_left.mp miss (sub up) hit

/-- Local one-sided charts on the frontier also supply the connected
patch needed at ordinary points of the closed domain. -/
theorem plane_domain_closure_connected_sides {W : Set ℂ} (op : IsOpen W)
    (sides : ∀ x∈frontier W, ∀ G : Set ℂ, IsOpen G → x∈G →
      ∃ O : Set ℂ, IsOpen O ∧ x∈O ∧ O⊆G ∧ IsPreconnected (O∩W)) :
    ∀ x∈closure W, ∀ G : Set ℂ, IsOpen G → x∈G →
      ∃ O : Set ℂ, IsOpen O ∧ x∈O ∧ O⊆G ∧ IsPreconnected (O∩W) := by
  intro x cx G og xg
  by_cases wx : x∈W
  · obtain ⟨r,rp,sub⟩ := Metric.mem_nhds_iff.mp ((og.inter op).mem_nhds ⟨xg,wx⟩)
    refine ⟨ball x r,isOpen_ball,mem_ball_self rp,sub.trans inter_subset_left,?_⟩
    rw [inter_eq_left.mpr (sub.trans inter_subset_right)]
    exact (convex_ball x r).isPreconnected
  · exact sides x ⟨cx,fun h => wx (interior_subset h)⟩ G og xg

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.boundary_convergence_of_shrinking_cuts
#print axioms TwoAxisHelicoid.plane_domain_closure_connected_sides
