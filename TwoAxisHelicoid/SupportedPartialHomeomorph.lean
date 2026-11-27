import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Homeomorph.Defs

namespace TwoAxisHelicoid
open Set Filter
open scoped Topology

/-- Extend a local spatial map by the identity outside its domain. -/
noncomputable def extendPartialMap {Y : Type*} [TopologicalSpace Y]
    (e : OpenPartialHomeomorph Y Y) (x : Y) : Y := by
  classical
  exact if x ∈ e.source then e x else x

theorem extendPartialMap_of_mem {Y : Type*} [TopologicalSpace Y]
    (e : OpenPartialHomeomorph Y Y) {x : Y} (hx : x ∈ e.source) : extendPartialMap e x = e x := by
  simp only [extendPartialMap,ite_eq_left hx]

theorem extendPartialMap_of_not_mem {Y : Type*} [TopologicalSpace Y]
    (e : OpenPartialHomeomorph Y Y) {x : Y} (hx : x ∉ e.source) : extendPartialMap e x = x := by
  simp only [extendPartialMap,ite_eq_right hx]

theorem extendPartialMap_fixes {Y : Type*} [TopologicalSpace Y]
    (e : OpenPartialHomeomorph Y Y) {K : Set Y}
    (hfix : ∀ x ∈ e.source, x ∉ K → e x = x) {x : Y} (hx : x ∉ K) :
    extendPartialMap e x = x := by
  by_cases hs : x ∈ e.source
  · rw [extendPartialMap_of_mem e hs]
    exact hfix x hs hx
  · exact extendPartialMap_of_not_mem e hs

theorem extendPartialMap_continuous {Y : Type*} [TopologicalSpace Y]
    (e : OpenPartialHomeomorph Y Y) {K : Set Y} (hK : IsClosed K) (hKU : K ⊆ e.source)
    (hfix : ∀ x ∈ e.source, x ∉ K → e x = x) : Continuous (extendPartialMap e) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ e.source
  · have he : extendPartialMap e =ᶠ[𝓝 x] e := by
      filter_upwards [e.open_source.mem_nhds hx] with y hy
      exact extendPartialMap_of_mem e hy
    exact (e.continuousOn.continuousAt (e.open_source.mem_nhds hx)).congr_of_eventuallyEq he
  · have hn : x ∉ K := fun h => hx (hKU h)
    have he : extendPartialMap e =ᶠ[𝓝 x] id := by
      filter_upwards [hK.isOpen_compl.mem_nhds hn] with y hy
      exact extendPartialMap_fixes e hfix hy
    exact continuousAt_id.congr_of_eventuallyEq he

/-- A local homeomorphism preserving its open domain and equal to the
identity outside a closed subset of that domain extends to an actual
global homeomorphism. The closed subset need not be compact. -/
noncomputable def extendSupportedHomeomorph {Y : Type*} [TopologicalSpace Y]
    (e : OpenPartialHomeomorph Y Y) (hU : e.source = e.target)
    {K : Set Y} (hK : IsClosed K) (hKU : K ⊆ e.source)
    (hfix : ∀ x ∈ e.source, x ∉ K → e x = x) : Y ≃ₜ Y where
  toFun := extendPartialMap e
  invFun := extendPartialMap e.symm
  left_inv x := by
    by_cases hx : x ∈ e.source
    · rw [extendPartialMap_of_mem e hx,extendPartialMap_of_mem e.symm (e.map_source hx)]
      exact e.left_inv hx
    · have ht : x ∉ e.symm.source := by simpa only [OpenPartialHomeomorph.symm_source,← hU] using hx
      rw [extendPartialMap_of_not_mem e hx,extendPartialMap_of_not_mem e.symm ht]
  right_inv x := by
    by_cases hx : x ∈ e.target
    · rw [extendPartialMap_of_mem e.symm hx,extendPartialMap_of_mem e (e.map_target hx)]
      exact e.right_inv hx
    · have hs : x ∉ e.source := by simpa only [hU] using hx
      rw [extendPartialMap_of_not_mem e.symm hx,extendPartialMap_of_not_mem e hs]
  continuous_toFun := extendPartialMap_continuous e hK hKU hfix
  continuous_invFun := by
    apply extendPartialMap_continuous e.symm hK
    · simpa only [OpenPartialHomeomorph.symm_source,← hU] using hKU
    · intro x hx hn
      have hs : x ∈ e.source := by simpa only [OpenPartialHomeomorph.symm_source,← hU] using hx
      have hi := e.left_inv hs
      rwa [hfix x hs hn] at hi

/-- Joint continuity survives identity extension when the supporting
closed set and the open coordinate domain are fixed throughout a family. -/
theorem extendPartialMap_family_continuous {T Y : Type*} [TopologicalSpace T] [TopologicalSpace Y]
    (e : T → OpenPartialHomeomorph Y Y) {U K : Set Y} (hU : IsOpen U) (hK : IsClosed K)
    (hKU : K ⊆ U) (hsource : ∀ t, (e t).source = U)
    (hfix : ∀ t x, x ∈ U → x ∉ K → e t x = x)
    (hjoint : ContinuousOn (fun q : T × Y => e q.1 q.2) (univ ×ˢ U)) :
    Continuous (fun q : T × Y => extendPartialMap (e q.1) q.2) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  by_cases hq : q.2 ∈ U
  · have hdom : univ ×ˢ U ∈ 𝓝 q := (isOpen_univ.prod hU).mem_nhds ⟨mem_univ _,hq⟩
    have he : (fun q : T × Y => extendPartialMap (e q.1) q.2) =ᶠ[𝓝 q]
        (fun q => e q.1 q.2) := by
      filter_upwards [hdom] with p hp
      exact extendPartialMap_of_mem (e p.1) (by rw [hsource]; exact hp.2)
    exact (hjoint.continuousAt hdom).congr_of_eventuallyEq he
  · have hn : q.2 ∉ K := fun h => hq (hKU h)
    have he : (fun q : T × Y => extendPartialMap (e q.1) q.2) =ᶠ[𝓝 q] Prod.snd := by
      filter_upwards [continuous_snd.continuousAt.eventually (hK.isOpen_compl.mem_nhds hn)] with p hp
      apply extendPartialMap_fixes (e p.1) (K := K) _ hp
      intro x hx hxK
      exact hfix p.1 x (by rwa [hsource] at hx) hxK
    exact continuous_snd.continuousAt.congr_of_eventuallyEq he

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.extendSupportedHomeomorph
#print axioms TwoAxisHelicoid.extendPartialMap_family_continuous
