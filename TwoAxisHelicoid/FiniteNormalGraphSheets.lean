import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Separation.Hausdorff

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology

/-- Local finite graphs over a base point. The section maps are used
only as germs. The equality of sets says these graphs exhaust the
surface in the selected tube, with no prescribed global number of sheets. -/
structure FiniteSheetGerms {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B) (b : B) where
  extraSheets : ℕ
  sheet : Fin (extraSheets+1) → B → E
  continuousAt : ∀ i, ContinuousAt (sheet i) b
  distinct : Function.Injective (fun i => sheet i b)
  fiber : ∀ᶠ v in 𝓝 b, p ⁻¹' {v} = range (fun i => sheet i v)

namespace FiniteSheetGerms
variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : E → B} {b : B}

theorem rightInverse (G : FiniteSheetGerms p b) (i : Fin (G.extraSheets+1)) :
    ∀ᶠ v in 𝓝 b, p (G.sheet i v) = v := by
  filter_upwards [G.fiber] with v hv
  exact (show G.sheet i v ∈ p ⁻¹' {v} from hv ▸ mem_range_self i)

theorem exists_sheet (G : FiniteSheetGerms p b) {x : E} (h : p x = b) :
    ∃ i, G.sheet i b = x := by
  apply G.fiber.self_of_nhds ▸ (show x ∈ p ⁻¹' {b} from h)

theorem inverseGerm [T2Space E] (G : FiniteSheetGerms p b) (hp : Continuous p)
    {x : E} (hx : p x = b) {i : Fin (G.extraSheets+1)} (hi : G.sheet i b = x) :
    ∀ᶠ a in 𝓝 x, G.sheet i (p a) = a := by
  have hpb : Tendsto p (𝓝 x) (𝓝 b) := hx ▸ hp.continuousAt
  have exclude (j : Fin (G.extraSheets+1)) : ∀ᶠ a in 𝓝 x, j ≠ i → G.sheet j (p a) ≠ a := by
    by_cases hji : j = i
    · exact Eventually.of_forall fun _ h => (h hji).elim
    · have hne : G.sheet j b ≠ x := fun h => hji (G.distinct (h.trans hi.symm))
      have hcont : ContinuousAt (fun a => G.sheet j (p a)) x := by
        exact (G.continuousAt j).comp_of_eq hp.continuousAt hx
      have not_eq : (fun a => G.sheet j (p a)) x ≠ id x := by simpa only [hx,id_eq] using hne
      exact ((hcont.ne_iff_eventually_ne continuousAt_id).mp not_eq).mono fun a ha _ => ha
  filter_upwards [hpb G.fiber,eventually_all.mpr exclude] with a ha hb
  have h : a ∈ range (fun j => G.sheet j (p a)) := ha ▸ (show a ∈ p ⁻¹' {p a} from rfl)
  obtain ⟨j,hj⟩ := h
  by_cases hji : j = i
  · simpa only [hji] using hj
  · exact (hb j hji hj).elim

end FiniteSheetGerms

/-- A locally exhaustive finite family of disjoint graphs makes its
continuous projection proper, surjective and a local homeomorphism. -/
theorem proper_projection_of_finite_sheet_germs {E B : Type*} [TopologicalSpace E] [T2Space E]
    [TopologicalSpace B] {p : E → B} (hp : Continuous p) (G : ∀ b, FiniteSheetGerms p b) :
    IsProperMap p ∧ IsLocalHomeomorph p ∧ Function.Surjective p := by
  have hopen : IsOpenMap p := by
    intro U hU
    rw [isOpen_iff_mem_nhds]
    rintro b ⟨x,hx,hb⟩
    obtain ⟨i,hi⟩ := (G b).exists_sheet hb
    have hmem := ((G b).continuousAt i) (hU.mem_nhds (hi ▸ hx))
    filter_upwards [hmem,(G b).rightInverse i] with v hv he
    exact ⟨_,hv,he⟩
  have hclosed : IsClosedMap p := by
    intro C hC
    rw [← isOpen_compl_iff,isOpen_iff_mem_nhds]
    intro b hb
    have hout (i : Fin ((G b).extraSheets+1)) : ∀ᶠ v in 𝓝 b, (G b).sheet i v ∉ C := by
      have hn : (G b).sheet i b ∈ Cᶜ :=
        fun he => hb ⟨_,he,((G b).rightInverse i).self_of_nhds⟩
      exact (G b).continuousAt i (hC.isOpen_compl.mem_nhds hn)
    filter_upwards [(G b).fiber,eventually_all.mpr hout] with v hv ha
    rintro ⟨x,hx,hpx⟩
    have hx' : x ∈ range (fun i => (G b).sheet i v) := hv ▸ (show x ∈ p ⁻¹' {v} from hpx)
    obtain ⟨i,rfl⟩ := hx'
    exact ha i hx
  refine ⟨isProperMap_iff_isClosedMap_and_compact_fibers.mpr ⟨hp,hclosed,?_⟩,
    isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr ?_,fun b => ⟨_,((G b).rightInverse 0).self_of_nhds⟩⟩
  · intro b
    rw [(G b).fiber.self_of_nhds]
    exact (finite_range _).isCompact
  · intro x
    obtain ⟨i,hi⟩ := (G (p x)).exists_sheet (x := x) rfl
    obtain ⟨U,hU,ho,hx⟩ := mem_nhds_iff.mp ((G (p x)).inverseGerm hp rfl hi)
    refine ⟨U,ho.mem_nhds hx,IsOpenEmbedding.of_continuous_injective_isOpenMap
      (hp.comp continuous_subtype_val) ?_ (hopen.comp ho.isOpenMap_subtype_val)⟩
    intro a b hab
    exact Subtype.ext ((hU a.2).symm.trans ((congrArg ((G (p x)).sheet i) hab).trans (hU b.2)))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.proper_projection_of_finite_sheet_germs
