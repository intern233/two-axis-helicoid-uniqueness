import TwoAxisHelicoid.ImmersionAtlas
import Mathlib.Topology.Homeomorph.Lemmas

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology ContDiff

/-- Construct an actual surface chart from a local ambient parametrization
and its coordinate inverse. The inherited topology is retained. -/
theorem exists_embedded_parametrization_chart
    {M A E : Type*} [TopologicalSpace M] [Nonempty M]
    [TopologicalSpace A] [TopologicalSpace E] {F : M → A}
    (hF : IsEmbedding F) (P : A → E) (G : E → A) (U : Set M) (V : Set E)
    (hU : IsOpen U) (hV : IsOpen V)
    (hcP : ContinuousOn (P ∘ F) U) (hcG : ContinuousOn G V)
    (hP : MapsTo (P ∘ F) U V)
    (hL : ∀ x ∈ U, G (P (F x)) = F x)
    (hR : ∀ y ∈ V, P (G y) = y)
    (hG : ∀ y ∈ V, ∃ x ∈ U, F x = G y) :
    ∃ e : OpenPartialHomeomorph M E, e.source = U ∧ e.target = V ∧
      (e : M → E) = P ∘ F ∧ ∀ y ∈ V, F (e.symm y) = G y := by
  let r : E → M := Function.invFun F ∘ G
  have hFr (y : E) (hy : y ∈ V) : F (r y) = G y :=
    Function.invFun_eq (by obtain ⟨x,_hx,hx⟩ := hG y hy; exact ⟨x,hx⟩)
  have hrc : ContinuousOn r V := by
    apply hF.continuousOn_iff.mpr
    exact hcG.congr hFr
  let e : OpenPartialHomeomorph M E :=
    { toFun := P ∘ F
      invFun := r
      source := U
      target := V
      map_source' := hP
      map_target' := by
        intro y hy
        obtain ⟨x,hx,hxy⟩ := hG y hy
        have hrx : r y = x := hF.injective ((hFr y hy).trans hxy.symm)
        exact hrx ▸ hx
      left_inv' := by
        intro x hx
        change Function.invFun F (G (P (F x))) = x
        rw [hL x hx]
        exact Function.leftInverse_invFun hF.injective x
      right_inv' := by
        intro y hy
        change P (F (r y)) = y
        rw [hFr y hy,hR y hy]
      open_source := hU
      open_target := hV
      continuousOn_toFun := hcP
      continuousOn_invFun := hrc }
  exact ⟨e,rfl,rfl,rfl,hFr⟩

theorem regularImmersionChart_of_parametrization
    {M E A : Type*} [TopologicalSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    {F : M → A} (e : OpenPartialHomeomorph M E) {G : E → A}
    (hG : ∀ y ∈ e.target, F (e.symm y) = G y)
    (hGc : ∀ y ∈ e.target, ContDiffAt ℝ ∞ G y)
    (hGi : ∀ y ∈ e.target, Function.Injective (fderiv ℝ G y)) :
    RegularImmersionChart F e := by
  intro y hy
  have he : F ∘ e.symm =ᶠ[𝓝 y] G := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact hG z hz
  exact ⟨(hGc y hy).congr_of_eventuallyEq he,by rw [he.fderiv_eq]; exact hGi y hy⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.exists_embedded_parametrization_chart
#print axioms TwoAxisHelicoid.regularImmersionChart_of_parametrization

