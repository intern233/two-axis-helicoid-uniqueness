import TwoAxisHelicoid.CompactParameterDoublePoints
import TwoAxisHelicoid.CompactCoincidentSheets

namespace TwoAxisHelicoid
open Set Filter Topology

/-- Injectivity propagates on a connected parameter space when double
points are uniformly confined locally and all limit contacts of separated
members are genuine coincidences of the local sheet images. This isolates
the geometric first-contact condition in the López–Ros argument. -/
theorem connected_family_injective_of_coincident_contacts {T M E : Type*}
    [TopologicalSpace T] [PreconnectedSpace T] [TopologicalSpace M] [T2Space M]
    [PreconnectedSpace M] [NoncompactSpace M] [TopologicalSpace E] [T2Space E]
    (F : T → M → E) (joint : Continuous (fun p : T × M => F p.1 p.2))
    (charts : ∀ (t : T) (x : M), ∃ V ∈ 𝓝 t, ∃ U ∈ 𝓝 x, ∀ s ∈ V, InjOn (F s) U)
    (tight : ∀ t : T, ∃ K : Set (M × M), IsCompact K ∧ ∀ᶠ s in 𝓝 t, immersionDoublePoints (F s) ⊆ K)
    (contact : ∀ t : T, (∃ᶠ s in 𝓝 t, Function.Injective (F s)) →
      ∀ x y : M, x ≠ y → F t x=F t y → ∀ V ∈ 𝓝 y, ∀ᶠ p in 𝓝 x, F t p ∈ F t '' V)
    {t₀ : T} (h₀ : Function.Injective (F t₀)) : ∀ s, Function.Injective (F s) := by
  let S := {t : T | Function.Injective (F t)}
  have op : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    obtain ⟨K,hK,hb⟩ := tight t
    exact injectivity_open_from_uniform_compact_pairs F ht (fun _ => joint.continuousAt) (charts t) hK hb
  have cl : IsClosed S := by
    rw [← closure_subset_iff_isClosed]
    intro t ht
    obtain ⟨K,hK,hb⟩ := tight t
    have loc (x : M) : ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ InjOn (F t) U := by
      obtain ⟨V,hV,U,hU,hi⟩ := charts t x
      exact ⟨interior U,isOpen_interior,mem_interior_iff_mem_nhds.mpr hU,(hi t (mem_of_mem_nhds hV)).mono interior_subset⟩
    apply injective_of_compact_coincident_sheet_germs (F t) (joint.comp (f := fun u : M => (t,u)) (by fun_prop))
      loc hK hb.self_of_nhds
    exact contact t (mem_closure_iff_frequently.mp ht)
  have all : S=univ := (isClopen_iff.mp ⟨cl,op⟩).resolve_left (show S.Nonempty from ⟨t₀,h₀⟩).ne_empty
  intro s
  exact (all ▸ mem_univ s : s ∈ S)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.connected_family_injective_of_coincident_contacts
