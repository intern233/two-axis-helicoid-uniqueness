import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Connected.Basic

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology OnePoint

/-- Collapsing the complement of an open coordinate to infinity is
continuous. This uses compact sets in the coordinate to control
continuity at every point of its boundary. -/
theorem open_embedding_collapse {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {j : X → Y} (emb : IsOpenEmbedding j) :
    ∃ f : Y → OnePoint X, Continuous f ∧ (∀ x : X, f (j x)=x) ∧ ∀ y∉range j, f y=∞ := by
  classical
  let f : Y → OnePoint X := fun y => if h : y∈range j then ↑h.choose else ∞
  have on (x : X) : f (j x)=x := by
    dsimp [f]
    rw [dite_eq_left (mem_range_self _)]
    exact congrArg OnePoint.some (emb.injective (Classical.choose_spec (mem_range_self x : j x∈range j)))
  have off (y : Y) (h : y∉range j) : f y=∞ := dite_eq_right h
  have pre {A : Set (OnePoint X)} (miss : ∞∉A) : f ⁻¹' A=j '' ((↑) ⁻¹' A : Set X) := by
    ext y
    constructor
    · intro h
      by_cases inJ : y∈range j
      · obtain ⟨x,rfl⟩ := inJ
        exact ⟨x,show (↑x : OnePoint X)∈A from (on x) ▸ (show f (j x)∈A from h),rfl⟩
      · exact (miss (off y inJ ▸ h)).elim
    · rintro ⟨x,h,rfl⟩
      change f (j x)∈A
      rwa [on]
  refine ⟨f,continuous_def.mpr ?_,on,off⟩
  intro A oa
  by_cases inf : ∞∈A
  · have compact := ((OnePoint.isOpen_iff_of_mem inf).mp oa).2
    have closed : IsClosed (f ⁻¹' Aᶜ) := by
      rw [pre (A := Aᶜ) (fun h => h inf)]
      exact (compact.image emb.continuous).isClosed
    simpa only [preimage_compl,compl_compl] using closed.isOpen_compl
  · rw [pre inf]
    exact emb.isOpenMap _ (OnePoint.isOpen_def.mp oa).2

/-- If a component with connected complement in a larger surface
lies in a plane chart, its complement in the Riemann sphere is
connected as well. -/
theorem chart_spherical_complement_preconnected {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {j : X → Y} (emb : IsOpenEmbedding j) {V : Set Y} (inside : V⊆range j)
    (outside : IsPreconnected Vᶜ) (extra : ∃ y, y∉range j) :
    IsPreconnected ((OnePoint.some : X → OnePoint X) '' (j ⁻¹' V))ᶜ := by
  obtain ⟨f,cf,on,off⟩ := open_embedding_collapse emb
  have eq : f '' Vᶜ=((OnePoint.some : X → OnePoint X) '' (j ⁻¹' V))ᶜ := by
    ext z
    induction z using OnePoint.rec with
    | infty =>
      constructor
      · intro _
        exact OnePoint.infty_notMem_image_coe
      · intro _
        obtain ⟨y,hy⟩ := extra
        exact ⟨y,fun h => hy (inside h),off y hy⟩
    | coe x =>
      constructor
      · rintro ⟨y,hy,yx⟩ ⟨a,ha,ax⟩
        have aj : a=x := OnePoint.coe_injective ax
        subst a
        by_cases hj : y∈range j
        · obtain ⟨b,rfl⟩ := hj
          have bx : b=x := OnePoint.coe_injective ((on b).symm.trans yx)
          exact hy (bx ▸ ha)
        · exact OnePoint.coe_ne_infty x (yx.symm.trans (off y hj))
      · intro h
        exact ⟨j x,fun hx => h ⟨x,hx,rfl⟩,on x⟩
  exact eq ▸ outside.image f cf.continuousOn

/-- The added end belongs to the closure of the exterior of any
relatively compact portion, so filling it preserves preconnectedness
of the complementary set. -/
theorem one_point_complement_of_relatively_compact {M : Type*} [TopologicalSpace M]
    [T2Space M] [NoncompactSpace M] {V : Set M} (k : IsCompact (closure V)) (outside : IsPreconnected Vᶜ) :
    IsPreconnected ((OnePoint.some : M → OnePoint M) '' V)ᶜ := by
  have lim : Tendsto (OnePoint.some : M → OnePoint M) (cocompact M) (𝓝 ∞) :=
    Filter.coclosedCompact_eq_cocompact (X := M) ▸ OnePoint.tendsto_coe_infty
  have edge : ∞∈closure ((OnePoint.some : M → OnePoint M) '' Vᶜ) := by
    apply mem_closure_of_tendsto lim
    filter_upwards [k.compl_mem_cocompact] with x hx
    exact mem_image_of_mem _ (fun h => hx (subset_closure h))
  have eq : ((OnePoint.some : M → OnePoint M) '' V)ᶜ=insert ∞ ((OnePoint.some : M → OnePoint M) '' Vᶜ) := by
    ext z
    induction z using OnePoint.rec with
    | infty => simp
    | coe x => simp
  rw [eq]
  exact (outside.image _ OnePoint.continuous_coe.continuousOn).subset_closure (subset_insert _ _) (insert_subset edge subset_closure)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.open_embedding_collapse
#print axioms TwoAxisHelicoid.chart_spherical_complement_preconnected
#print axioms TwoAxisHelicoid.one_point_complement_of_relatively_compact
