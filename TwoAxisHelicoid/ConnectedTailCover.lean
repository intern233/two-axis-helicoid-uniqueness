import TwoAxisHelicoid.OrderedProperCover

namespace TwoAxisHelicoid
open Set

/-- A clopen part of a proper local homeomorphism onto a connected base
has either empty or full image. -/
theorem proper_local_homeomorph_clopen_image {E B : Type*}
    [TopologicalSpace E] [TopologicalSpace B] [PreconnectedSpace B]
    {f : E → B} (hp : IsProperMap f) (hl : IsLocalHomeomorph f)
    {S : Set E} (hS : IsClopen S) (hne : S.Nonempty) : f '' S = univ :=
  (show IsClopen (f '' S) from ⟨hp.isClosedMap S hS.isClosed,hl.isOpenMap S hS.isOpen⟩).eq_univ
    (hne.image f)

/-- If one complete fiber lies in a connected part of the source, every
clopen part of the source is empty or full. In the end application this
connected set is a subend, and the fiber is chosen far beyond its compact
complement. Source connectedness is a conclusion, not an input. -/
theorem proper_local_homeomorph_preconnected_of_connected_full_fiber {E B : Type*}
    [TopologicalSpace E] [TopologicalSpace B] [PreconnectedSpace B]
    {f : E → B} (hp : IsProperMap f) (hl : IsLocalHomeomorph f)
    {U : Set E} (hU : IsPreconnected U) (b : B) (hfull : f ⁻¹' {b} ⊆ U) :
    PreconnectedSpace E := by
  apply preconnectedSpace_iff_clopen.mpr
  intro S hS
  rcases S.eq_empty_or_nonempty with hempty | hne
  · exact Or.inl hempty
  right
  rcases Sᶜ.eq_empty_or_nonempty with hempty | hcne
  · simpa only [compl_empty,compl_compl] using congrArg (fun T : Set E => Tᶜ) hempty
  have himg := proper_local_homeomorph_clopen_image hp hl hS hne
  have hcimg := proper_local_homeomorph_clopen_image hp hl hS.compl hcne
  obtain ⟨e,he,heb⟩ := show b ∈ f '' S by rw [himg]; trivial
  obtain ⟨d,hd,hdb⟩ := show b ∈ f '' Sᶜ by rw [hcimg]; trivial
  have heU : e ∈ U := hfull heb
  have hdU : d ∈ U := hfull hdb
  have hsplit := IsPreconnected.subset_or_subset hS.isOpen hS.compl.isOpen
    disjoint_compl_right (show U ⊆ S ∪ Sᶜ by rw [union_compl_self]; exact subset_univ _) hU
  rcases hsplit with hs | hs
  · exact False.elim (hd (hs hdU))
  · exact False.elim (hs heU he)

/-- The one-sheet step needs only one connected subend containing a full
fiber, together with properness, local invertibility and the actual height
ordering. -/
theorem ordered_proper_local_homeomorph_injective_of_connected_full_fiber {E B : Type*}
    [TopologicalSpace E] [TopologicalSpace B] [PreconnectedSpace B]
    {f : E → B} {h : E → ℝ} (hp : IsProperMap f) (hh : Continuous h)
    (hl : IsLocalHomeomorph f)
    (hsep : ∀ d e, f d = f e → h d = h e → d = e)
    {U : Set E} (hU : IsPreconnected U) (b : B) (hfull : f ⁻¹' {b} ⊆ U) :
    Function.Injective f := by
  let := proper_local_homeomorph_preconnected_of_connected_full_fiber hp hl hU b hfull
  exact connected_ordered_proper_local_homeomorph_injective hp hh hl hsep

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.ordered_proper_local_homeomorph_injective_of_connected_full_fiber
