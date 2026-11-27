import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.OpenPartialHomeomorph.Continuity

namespace TwoAxisHelicoid
open Set Metric Topology

/-- A Euclidean coordinate neighborhood centered at the chosen point,
with its whole model space as domain. -/
theorem centered_euclidean_chart_neighborhood {M E : Type*} [TopologicalSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph M E) {p : M} (hp : p ∈ e.source) :
    ∃ (V : Set M) (H : E ≃ₜ V), IsOpen V ∧ p ∈ V ∧ V ⊆ e.source ∧ (H 0).1 = p := by
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds (e.map_source hp))
  let u := OpenPartialHomeomorph.univBall (E := E) (e p) r
  have hsu (x : E) : x ∈ u.source := by simp [u]
  have htu : u.target = ball (e p) r := OpenPartialHomeomorph.univBall_target _ hr
  have hu (x : E) : u x ∈ ball (e p) r := htu ▸ u.map_source (hsu x)
  let V := e.symm '' ball (e p) r
  have hV : IsOpen V := e.isOpen_image_symm_of_subset_target isOpen_ball hsub
  have hpV : p ∈ V := ⟨e p,mem_ball_self hr,e.left_inv hp⟩
  have hvs : V ⊆ e.source := by rintro x ⟨w,hw,rfl⟩; exact e.map_target (hsub hw)
  have hvu (x : V) : e x.1 ∈ u.target := by
    obtain ⟨w,hw,heq⟩ := x.2
    rw [← heq,e.right_inv (hsub hw),htu]
    exact hw
  let H : E ≃ₜ V := {
    toFun := fun w => ⟨e.symm (u w),u w,hu w,rfl⟩
    invFun := fun v => u.symm (e v.1)
    left_inv := fun w => by
      change u.symm (e (e.symm (u w))) = w
      rw [e.right_inv (hsub (hu w)),u.left_inv (hsu w)]
    right_inv := fun v => Subtype.ext (by
      change e.symm (u (u.symm (e v.1))) = v.1
      rw [u.right_inv (hvu v),e.left_inv (hvs v.2)])
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply continuous_iff_continuousAt.mpr
      intro w
      exact (e.symm.continuousAt (hsub (hu w))).comp (f := u) (u.continuousAt (hsu w))
    continuous_invFun := by
      apply continuous_iff_continuousAt.mpr
      intro v
      have hec : ContinuousAt (fun v : V => e v.1) v := (e.continuousAt (hvs v.2)).comp
        (f := (Subtype.val : V → M)) continuous_subtype_val.continuousAt
      exact (u.symm.continuousAt (hvu v)).comp (f := fun v : V => e v.1) hec }
  have h0 : (H 0).1 = p := by change e.symm (u 0) = p; rw [OpenPartialHomeomorph.univBall_apply_zero,e.left_inv hp]
  exact ⟨V,H,hV,hpV,hvs,h0⟩

/-- A connected punctured plane neighborhood in any prescribed surface
chart. The returned parameterization is centered at the deleted point. -/
theorem centered_surface_chart_neighborhood {M E : Type*} [TopologicalSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (hdim : 1 < Module.rank ℝ E)
    (e : OpenPartialHomeomorph M E) {p : M} (hp : p ∈ e.source) :
    ∃ (V : Set M) (H : E ≃ₜ V), IsOpen V ∧ p ∈ V ∧ V ⊆ e.source ∧ (H 0).1 = p ∧
      IsConnected {v : V | v.1 ≠ p} := by
  obtain ⟨V,H,hV,hpV,hvs,h0⟩ := centered_euclidean_chart_neighborhood e hp
  refine ⟨V,H,hV,hpV,hvs,h0,?_⟩
  have hImage : H '' ({0}ᶜ : Set E) = {v : V | v.1 ≠ p} := by
    ext v
    constructor
    · rintro ⟨w,hw,rfl⟩ heq
      exact hw (H.injective (Subtype.ext (heq.trans h0.symm)))
    · intro hv
      refine ⟨H.symm v,?_,H.apply_symm_apply v⟩
      intro he
      apply hv
      have h : H (H.symm v) = H 0 := congrArg H he
      simpa only [H.apply_symm_apply] using (congrArg Subtype.val h).trans h0
  rw [← hImage]
  exact (isPathConnected_compl_singleton_of_one_lt_rank hdim 0).isConnected.image H H.continuous.continuousOn

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.centered_surface_chart_neighborhood
