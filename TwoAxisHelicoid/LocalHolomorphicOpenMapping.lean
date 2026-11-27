import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.LocallyConstant.Basic

namespace TwoAxisHelicoid
open Complex Set Filter Topology Metric
open scoped Topology

/-- The open mapping theorem in local plane coordinates on an arbitrary
connected topological surface. A local coordinate need not be the same
as the default chart of the domain. -/
theorem open_of_nonconstant_in_holomorphic_coordinates {M : Type*} [TopologicalSpace M] [PreconnectedSpace M]
    (F : M → ℂ) (different : ∃ x y, F x≠F y)
    (chart : ∀ x, ∃ (e : OpenPartialHomeomorph M ℂ) (f : ℂ → ℂ), x∈e.source ∧ AnalyticAt ℂ f (e x) ∧ F=ᶠ[𝓝 x] f ∘ e) :
    IsOpenMap F := by
  let T := {x | ∀ᶠ y in 𝓝 x, F y=F x}
  have patches (x : M) : ∃ V : Set M, IsOpen V ∧ x∈V ∧
      (V⊆T ∨ (∀ W⊆V, IsOpen W → IsOpen (F '' W))) := by
    obtain ⟨e,f,xs,hf,germ⟩ := chart x
    obtain ⟨r,rp,an⟩ := Metric.mem_nhds_iff.mp hf.eventually_analyticAt
    let B := ball (e x) r
    obtain ⟨W,inc,wo,xw⟩ := mem_nhds_iff.mp germ
    let V := W∩(e.source∩e ⁻¹' B)
    have vo : IsOpen V := wo.inter (e.isOpen_inter_preimage isOpen_ball)
    have xv : x∈V := ⟨xw,xs,mem_ball_self rp⟩
    refine ⟨V,vo,xv,?_⟩
    have analytic : AnalyticOnNhd ℂ f B := fun _ hy => an hy
    rcases analytic.is_constant_or_isOpen (convex_ball _ _).isPreconnected with ⟨c,eq⟩|op
    · left
      intro y hy
      filter_upwards [vo.mem_nhds hy] with z hz
      exact (inc hz.1).trans ((eq _ hz.2.2).trans ((inc hy.1).trans (eq _ hy.2.2)).symm)
    · right
      intro S sub so
      have p : F '' S=f '' (e '' S) := by
        rw [image_image]
        exact image_congr (fun y hy => inc (sub hy).1)
      rw [p]
      apply op _ (image_subset_iff.mpr (fun _ hs => (sub hs).2.2))
      exact e.isOpen_image_of_subset_source so (fun _ hs => (sub hs).2.1)
  have avoid {V : Set M} (vo : IsOpen V) (op : ∀ W⊆V, IsOpen W → IsOpen (F '' W)) : V⊆Tᶜ := by
    intro y hy loc
    obtain ⟨W,eq,wo,yw⟩ := mem_nhds_iff.mp loc
    have same : F '' (W∩V)={F y} := by
      apply Subset.antisymm
      · rintro _ ⟨z,hz,rfl⟩
        exact mem_singleton_iff.mpr (eq hz.1)
      · exact singleton_subset_iff.mpr ⟨y,⟨yw,hy⟩,rfl⟩
    exact not_isOpen_singleton (F y) (same ▸ op _ inter_subset_right (wo.inter vo))
  have to' : IsOpen T := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    obtain ⟨W,wo,yw,inside|op⟩ := patches y
    · exact mem_of_superset (wo.mem_nhds yw) inside
    · exact (avoid wo op yw hy).elim
  have tc : IsClosed T := isOpen_compl_iff.mp (isOpen_iff_mem_nhds.mpr (by
    intro y hy
    obtain ⟨W,wo,yw,inside|op⟩ := patches y
    · exact (hy (inside yw)).elim
    · exact mem_of_superset (wo.mem_nhds yw) (avoid wo op)))
  have empty : T=∅ := by
    by_contra h
    have un := (show IsClopen T from ⟨tc,to'⟩).eq_univ (nonempty_iff_ne_empty.mpr h)
    have lc : IsLocallyConstant F := (IsLocallyConstant.iff_eventually_eq _).mpr (fun x => (show x∈T from un ▸ mem_univ x))
    obtain ⟨x,y,ne⟩ := different
    exact ne (lc.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ x) (mem_univ y))
  intro S so
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨V,vo,xv,inside|op⟩ := patches x
  · have impossible := inside xv
    rw [empty] at impossible
    exact impossible.elim
  · exact mem_of_superset ((op (V∩S) inter_subset_left (vo.inter so)).mem_nhds ⟨x,⟨xv,hx⟩,rfl⟩) (image_mono inter_subset_right)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.open_of_nonconstant_in_holomorphic_coordinates
