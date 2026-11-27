import TwoAxisHelicoid.ComplexExteriorConnected
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.Connected.Clopen

namespace TwoAxisHelicoid
open Set Metric Topology
open scoped OnePoint Topology

/-- Removing infinity from the connected spherical complement of a bounded
open plane set keeps it connected. Only one member of a disjoint closed
separation can meet the whole exterior of a sufficiently large disk. -/
theorem plane_complement_of_spherical_complement {W : Set ℂ} (op : IsOpen W)
    (bounded : IsCompact (closure W)) (conn : IsPreconnected ((OnePoint.some : ℂ → OnePoint ℂ) '' W)ᶜ) :
    IsPreconnected Wᶜ := by
  classical
  obtain ⟨B,b⟩ := bounded.isBounded.exists_norm_le
  let R := max B 0
  let T := {z : ℂ | R<‖z‖}
  have out : T⊆Wᶜ := fun x hx inside => (not_lt_of_ge ((b x (subset_closure inside)).trans (le_max_left _ _))) hx
  let c := (OnePoint.some : ℂ → OnePoint ℂ)
  let P := (c '' W)ᶜ
  have mem (z : ℂ) : c z∈P ↔ z∈Wᶜ := (OnePoint.coe_injective.mem_set_image).not
  apply (isPreconnected_iff_subset_of_fully_disjoint_closed op.isClosed_compl).mpr
  intro u v cu cv cover dis
  have oneSide {u v : Set ℂ} (cu : IsClosed u) (cv : IsClosed v) (cover : Wᶜ⊆u∪v)
      (dis : Disjoint u v) (big : T⊆u) : Wᶜ⊆u := by
    let A := insert (∞ : OnePoint ℂ) (c '' u)
    let V := Wᶜ∩v
    let D := c '' V
    have pre : c ⁻¹' A=u := by
      ext x
      simp only [A,mem_preimage,mem_insert_iff,c,OnePoint.coe_ne_infty,false_or,OnePoint.coe_injective.mem_set_image]
    have ca : IsClosed A := by
      apply (OnePoint.isClosed_iff_of_mem (mem_insert _ _)).mpr
      change IsClosed (c ⁻¹' A)
      rwa [pre]
    have bd : V⊆closedBall 0 R := by
      intro x hx
      rw [mem_closedBall,dist_zero_right]
      exact le_of_not_gt (fun h => disjoint_left.mp dis (big h) hx.2)
    have cd := ((isCompact_closedBall (0:ℂ) R).of_isClosed_subset (op.isClosed_compl.inter cv) bd).image OnePoint.continuous_coe
    have split : P⊆A∪D := by
      intro x hx
      induction x using OnePoint.rec with
      | infty => exact Or.inl (mem_insert _ _)
      | coe z =>
        have hz := (mem z).mp hx
        rcases cover hz with hit|hit
        · exact Or.inl (mem_insert_of_mem _ (mem_image_of_mem c hit))
        · exact Or.inr (mem_image_of_mem c ⟨hz,hit⟩)
    have sep : Disjoint A D := by
      apply disjoint_left.mpr
      rintro _ ha ⟨z,hz,rfl⟩
      exact disjoint_left.mp dis (show z∈u from pre ▸ (show z∈c ⁻¹' A from ha)) hz.2
    have unionClosed := isPreconnected_iff_subset_of_disjoint_closed.mp conn A D ca cd.isClosed split
      (by rw [sep.inter_eq,inter_empty])
    rcases unionClosed with all|miss
    · exact fun z hz => pre ▸ (show z∈c ⁻¹' A from all ((mem z).mpr hz))
    · exact (OnePoint.infty_notMem_image_coe (miss OnePoint.infty_notMem_image_coe)).elim
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp (complex_norm_exterior_isPreconnected (le_max_right B 0))
      u v cu cv (out.trans cover) (by rw [dis.inter_eq,inter_empty]) with hu|hv
  · exact Or.inl (oneSide cu cv cover dis hu)
  · exact Or.inr (oneSide cv cu (union_comm u v ▸ cover) dis.symm hv)

/-- In the plane the common boundary of a connected open set and its
connected complement is connected. A putative separation gives a circle
map whose real lift has incompatible values on the two closed pieces. -/
theorem connected_open_plane_frontier {W : Set ℂ} (op : IsOpen W)
    (inside : IsPreconnected W) (outside : IsPreconnected Wᶜ) : IsPreconnected (frontier W) := by
  classical
  let π : ℝ → AddCircle (1:ℝ) := (↑)
  have cp := AddCircle.isCoveringMap_coe (1:ℝ)
  have zero : π 0=0 := rfl
  have one : π 1=0 := AddCircle.coe_period (1:ℝ)
  apply (isPreconnected_iff_subset_of_fully_disjoint_closed isClosed_frontier).mpr
  intro u v cu cv sub dis
  by_contra! bad
  obtain ⟨x,xb,xv⟩ := Set.not_subset.mp bad.2
  obtain ⟨y,yb,yu⟩ := Set.not_subset.mp bad.1
  obtain ⟨h,h0,h1,_⟩ := exists_continuous_zero_one_of_isClosed cu cv dis
  have boundary (z : ℂ) (hz : z∈frontier W) : π (h z)=0 := by
    rcases sub hz with hu|hv
    · exact (congrArg π (h0 hu)).trans zero
    · exact (congrArg π (h1 hv)).trans one
  let f : C(ℂ,AddCircle (1:ℝ)) := ⟨fun z => if z∈W then π (h z) else 0,
    Continuous.if boundary (cp.continuous.comp h.continuous) continuous_const⟩
  have onCl (z : ℂ) (hz : z∈closure W) : f z=π (h z) := by
    by_cases w : z∈W
    · simp only [f,ContinuousMap.coe_mk,ite_eq_left w]
    · change (if z∈W then π (h z) else 0)=_
      rw [ite_eq_right w,boundary z ⟨hz,fun hi => w (interior_subset hi)⟩]
  have off (z : ℂ) (hz : z∈Wᶜ) : f z=0 := ite_eq_right hz
  have xout : x∈Wᶜ := op.interior_eq ▸ xb.2
  have yout : y∈Wᶜ := op.interior_eq ▸ yb.2
  obtain ⟨g,⟨gx,lift⟩,_⟩ := cp.existsUnique_continuousMap_lifts f x 0 (zero.trans (off x xout).symm)
  have eq (z : ℂ) : π (g z)=f z := congrFun lift z
  have xu : x∈u := (sub xb).resolve_right xv
  have yv : y∈v := (sub yb).resolve_left yu
  have on := cp.eqOn_of_comp_eqOn inside.closure g.continuous.continuousOn h.continuous.continuousOn
    (fun z hz => (eq z).trans (onCl z hz)) (frontier_subset_closure xb) (gx.trans (h0 xu).symm)
  have constant := cp.constOn_of_comp outside g.continuous.continuousOn
    (fun a ha b hb => (eq a).trans ((off a ha).trans ((off b hb).symm.trans (eq b).symm))) yout xout
  have both := (h1 yv).symm.trans ((on (frontier_subset_closure yb)).symm.trans (constant.trans gx))
  exact one_ne_zero (show (1:ℝ)=0 from both)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.plane_complement_of_spherical_complement
#print axioms TwoAxisHelicoid.connected_open_plane_frontier
