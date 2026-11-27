import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Set Filter Metric Topology

/-- Local normal coordinates on a compact embedded core give a single
positive tube width on an open neighborhood of the entire core. The
tube is an open embedding, hence has actual continuous base and signed
height coordinates. -/
theorem compact_core_uniform_open_tube {M E : Type*} [TopologicalSpace M] [TopologicalSpace E] [T2Space E]
    {F : M × ℝ → E} {K : Set M} (kc : IsCompact K) (base : InjOn (fun x => F (x,0)) K)
    (localT : IsLocalHomeomorphOn F (K ×ˢ ({0}:Set ℝ))) :
    ∃ (U : Set M) (r : ℝ), IsOpen U ∧ K⊆U ∧ 0<r ∧
      IsOpenEmbedding ((U ×ˢ ball (0:ℝ) r).domRestrict F) := by
  let S := K ×ˢ ({0}:Set ℝ)
  let good := {p : M × ℝ | ∃ e : OpenPartialHomeomorph (M × ℝ) E, p∈e.source ∧ F=e}
  have op : IsOpen good := isOpen_iff_mem_nhds.mpr fun p ⟨e,h,eq⟩ =>
    Filter.mem_of_superset (e.open_source.mem_nhds h) (fun q hq => ⟨e,hq,eq⟩)
  have si : InjOn F S := by
    rintro ⟨x,s⟩ ⟨hx,hs⟩ ⟨y,t⟩ ⟨hy,ht⟩ eq
    change s=0 at hs
    change t=0 at ht
    subst s; subst t
    exact Prod.ext (base hx hy eq) rfl
  obtain ⟨V,vo,sub,vi⟩ := si.exists_isOpen_superset (kc.prod isCompact_singleton)
    (fun x hx => by obtain ⟨e,h,eq⟩ := localT x hx; rw [eq]; exact e.continuousAt h)
    (fun x hx => by obtain ⟨e,h,eq⟩ := localT x hx; exact ⟨e.source,e.open_source.mem_nhds h,by rw [eq]; exact e.injOn⟩)
  obtain ⟨U,T,uo,to',us,ts,both⟩ := generalized_tube_lemma kc (isCompact_singleton (x := (0:ℝ)))
    (vo.inter op) (fun x hx => ⟨sub hx,localT x hx⟩)
  obtain ⟨r,rp,rt⟩ := Metric.mem_nhds_iff.mp (to'.mem_nhds (ts (mem_singleton _)))
  let W := U ×ˢ ball (0:ℝ) r
  have covered : W⊆V∩good := fun x hx => both ⟨hx.1,rt hx.2⟩
  have wo : IsOpen W := uo.prod isOpen_ball
  have interiorMap (x : W) : Filter.map (W.domRestrict F) (𝓝 x)=𝓝 (F x) := by
    obtain ⟨e,inside,eq⟩ := (covered x.2).2
    change Filter.map (F ∘ (Subtype.val : W → M × ℝ)) (𝓝 x)=_
    rw [← Filter.map_map,wo.isOpenEmbedding_subtypeVal.map_nhds_eq,eq,e.map_nhds_eq inside]
  refine ⟨U,r,uo,us,rp,isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr ⟨?_,?_,?_⟩⟩
  · exact continuous_iff_continuousAt.mpr fun x => (interiorMap x).le
  · exact injOn_iff_injective.mp (vi.mono fun x hx => (covered hx).1)
  · exact IsOpenMap.of_nhds_le fun x => (interiorMap x).ge

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_core_uniform_open_tube
