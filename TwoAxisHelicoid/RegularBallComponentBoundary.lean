import TwoAxisHelicoid.RegularCutHalfPlaneCharts
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

namespace TwoAxisHelicoid
open Set Filter Metric Topology
open scoped Topology

/-- The boundary of a component of a strict sublevel lies on the
level itself. Local connectedness excludes another component of the
same open sublevel from its closure. -/
theorem component_frontier_lies_on_level {M : Type*} [TopologicalSpace M] [LocallyConnectedSpace M]
    {f : M → ℝ} (cf : Continuous f) {r : ℝ} {p q : M} (boundary : q∈frontier (connectedComponentIn {y | f y<r} p)) :
    f q=r := by
  let U := {y | f y<r}
  let V := connectedComponentIn U p
  have openU : IsOpen U := isOpen_lt cf continuous_const
  have cl : q∈closure V := frontier_subset_closure boundary
  have small : V⊆{y | f y≤r} := fun y hy => (show f y<r from connectedComponentIn_subset U p hy).le
  have leq : f q≤r := closure_minimal small (isClosed_le cf continuous_const) cl
  apply le_antisymm leq (le_of_not_gt ?_)
  intro inside
  let W := connectedComponentIn U q
  have qW : q∈W := mem_connectedComponentIn inside
  obtain ⟨w,ww,wv⟩ := mem_closure_iff.mp cl W openU.connectedComponentIn qW
  have same : V=W := (connectedComponentIn_eq wv).trans (connectedComponentIn_eq ww).symm
  have qV : q∈V := same ▸ qW
  exact boundary.2 (openU.connectedComponentIn.interior_eq.symm ▸ qV)

/-- Each individual component touching a regular cut inherits the
full local half-plane, including its boundary line. The local chart
is obtained by restricting the original cutting coordinate. -/
theorem component_regular_half_plane {M : Type*} [TopologicalSpace M] {U : Set M} {p q : M}
    (near : q∈closure (connectedComponentIn U p)) (e : OpenPartialHomeomorph M (ℝ × ℝ))
    (inside : q∈e.source) (cut : ∀ x∈e.source, x∈U ↔ (e x).1<0) :
    ∃ d : OpenPartialHomeomorph M (ℝ × ℝ), q∈d.source ∧ (d : M → ℝ × ℝ)=e ∧
      d.IsImage (connectedComponentIn U p) (Iio 0 ×ˢ univ) ∧
      d.IsImage (closure (connectedComponentIn U p)) (Iic 0 ×ˢ univ) ∧
      d.IsImage (frontier (connectedComponentIn U p)) ({0} ×ˢ univ) := by
  let V := connectedComponentIn U p
  let H := Iio (0:ℝ) ×ˢ (univ : Set ℝ)
  obtain ⟨r,rp,sub⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds (e.map_source inside))
  let B := ball (e q) r
  let P := e.source ∩ e ⁻¹' B
  have op : IsOpen P := e.isOpen_inter_preimage isOpen_ball
  have qP : q∈P := ⟨inside,mem_ball_self rp⟩
  let W := e.symm '' (B∩H)
  have conn : IsPreconnected W := ((convex_ball (e q) r).inter ((convex_Iio _).prod convex_univ)).isPreconnected.image _
    (e.continuousOn_symm.mono fun _ hz => sub hz.1)
  have part : W⊆U := by
    rintro _ ⟨t,⟨hb,hh⟩,rfl⟩
    apply (cut _ (e.map_target (sub hb))).mpr
    rw [e.right_inv (sub hb)]
    exact hh.1
  obtain ⟨x,hx,xV⟩ := mem_closure_iff.mp near P op qP
  have ofneg (y : M) (hy : y∈P) (neg : (e y).1<0) : y∈W :=
    ⟨e y,⟨hy.2,neg,mem_univ _⟩,e.left_inv hy.1⟩
  have same : W⊆V := by
    change W⊆connectedComponentIn U p
    rw [connectedComponentIn_eq xV]
    exact conn.subset_connectedComponentIn (ofneg x hx ((cut _ hx.1).mp (connectedComponentIn_subset U p xV))) part
  let d := e.restr P
  have image : d.IsImage V H := by
    intro y hy
    have hp : y∈P := interior_subset hy.2
    exact ⟨fun h => same (ofneg y hp h.1),fun h => ⟨(cut _ hp.1).mp (connectedComponentIn_subset U p h),mem_univ _⟩⟩
  refine ⟨d,⟨inside,op.interior_eq.symm ▸ qP⟩,rfl,image,?_,?_⟩
  · simpa only [H,closure_prod_eq,closure_Iio,closure_univ] using image.closure
  · have bdy : frontier H=({0} : Set ℝ) ×ˢ (univ : Set ℝ) := by
      ext z
      change z∈frontier (Iio (0:ℝ) ×ˢ (univ : Set ℝ)) ↔ _
      rw [frontier,closure_prod_eq,closure_Iio,closure_univ,interior_prod_eq,isOpen_Iio.interior_eq,interior_univ]
      simp only [Set.mem_sdiff,mem_prod,mem_Iic,mem_univ,and_true,mem_Iio,not_lt,mem_singleton_iff]
      exact le_antisymm_iff.symm
    simpa only [bdy] using image.frontier

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.component_frontier_lies_on_level
#print axioms TwoAxisHelicoid.component_regular_half_plane
