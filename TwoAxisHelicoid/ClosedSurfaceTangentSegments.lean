import TwoAxisHelicoid.SmoothSurfaceOrbit

namespace TwoAxisHelicoid
open Set Filter Topology Metric
open scoped Topology NNReal

/-- A bounded ambient vector field that is tangent to a closed regular
surface has an integral segment through each point, including both endpoints. -/
theorem closed_surface_unit_time_orbit {S : Set (Fin 3 → ℝ)} (hS : IsClosed S)
    {V : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hV : ContDiff ℝ 1 V) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ y, ‖V y‖ ≤ B)
    (chart : ∀ x ∈ S, ∃ (X : ℂ → Fin 3 → ℝ) (z : ℂ), X z = x ∧
      ContDiffAt ℝ 2 X z ∧ Function.Injective (fderiv ℝ X z) ∧
      ∀ᶠ w in 𝓝 z, X w ∈ S ∧ ∃ v, fderiv ℝ X w v = V (X w))
    {x : Fin 3 → ℝ} (hx : x ∈ S) :
    ∃ γ : ℝ → Fin 3 → ℝ, γ 0 = x ∧ ∀ t ∈ Ioo (-1:ℝ) 2,
      γ t ∈ S ∧ HasDerivAt γ (V (γ t)) t := by
  let a : ℝ≥0 := ⟨2*(B+1),by positivity⟩
  let b : ℝ≥0 := ⟨B,hB⟩
  obtain ⟨K,hK⟩ := hV.contDiffOn.exists_lipschitzOnWith one_ne_zero
    (convex_closedBall x (a:ℝ)) (isCompact_closedBall x (a:ℝ))
  have hp : IsPicardLindelof (fun _ : ℝ => V) (tmin := -1) (tmax := 2)
      ⟨0,by norm_num⟩ x a 0 b K := by
    apply IsPicardLindelof.of_time_independent (fun y _ => hb y) hK
    change B*max ((2:ℝ)-0) (0-(-1)) ≤ 2*(B+1)-0
    norm_num
    linarith
  obtain ⟨γ,h0,hwithin⟩ := hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  let J := Ioo (-1:ℝ) 2
  have der (t) (ht : t ∈ J) : HasDerivAt γ (V (γ t)) t :=
    (hwithin t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  let P := {t : J | γ t.1 ∈ S}
  have ct : Continuous (fun t : J => γ t.1) :=
    continuous_iff_continuousAt.mpr fun t => (der _ t.2).continuousAt.comp continuous_subtype_val.continuousAt
  have closed : IsClosed P := hS.preimage ct
  have op : IsOpen P := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    obtain ⟨X,z,hz,hs,hi,htan⟩ := chart (γ t.1) ht
    have hd : ∀ᶠ s in 𝓝 t.1, HasDerivAt γ (V (γ s)) s := by
      filter_upwards [isOpen_Ioo.mem_nhds t.2] with s h
      exact der s h
    exact continuous_subtype_val.continuousAt.eventually
      (smooth_tangent_orbit_local hs hi (hV.contDiffAt) htan hd hz.symm)
  let : PreconnectedSpace J := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  have hmem : (⟨0,by norm_num [J]⟩ : J) ∈ P := by
    change γ 0 ∈ S
    rwa [h0]
  have hall : P = univ := IsClopen.eq_univ ⟨closed,op⟩ ⟨_,hmem⟩
  refine ⟨γ,h0,?_⟩
  intro t ht
  exact ⟨(show (⟨t,ht⟩ : J) ∈ P by rw [hall]; exact mem_univ _),der t ht⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.closed_surface_unit_time_orbit
