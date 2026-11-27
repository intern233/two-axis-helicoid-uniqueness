import TwoAxisHelicoid.PlaneChartOrientationCocycle
import TwoAxisHelicoid.OrientedMinimalManifold

namespace TwoAxisHelicoid
open Complex Matrix Filter Set Topology
open scoped ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M]

/-- Under a real change of regular immersion coordinates, the unit
tangent cross product changes by the topological local degree. -/
theorem immersion_normal_chartIndex {F : M → Fin 3 → ℝ} {e d : OpenPartialHomeomorph M ℂ}
    (hr : RegularImmersionChart F e) (hd : RegularImmersionChart F d) {x : M}
    (hex : x ∈ e.source) (hdx : x ∈ d.source) :
    normalizedTangentCross (F ∘ e.symm) (e x) =
      (planeChartIndex e d x : ℝ) • normalizedTangentCross (F ∘ d.symm) (d x) := by
  let f := e.symm.trans d
  let z := e x
  have hsrc : z ∈ f.source := planeChart_transition_source hex hdx
  have hfx : f z = d x := congrArg d (e.left_inv hex)
  have hY := (hd _ (d.map_source hdx)).1.differentiableAt (by simp)
  have hY' : DifferentiableAt ℝ (F ∘ d.symm) (f z) := hfx.symm ▸ hY
  have hf := (regularImmersionChart_transition hr hd hsrc).differentiableAt (by simp)
  have hfc : ∀ᶠ w in 𝓝 z, ContinuousAt f w :=
    (show ∀ᶠ w in 𝓝 z, w ∈ f.source from f.open_source.mem_nhds hsrc).mono fun _ hw => f.continuousAt hw
  have heq : (F ∘ e.symm) =ᶠ[𝓝 z] (F ∘ d.symm) ∘ f := by
    filter_upwards [f.open_source.mem_nhds hsrc] with w hw
    exact congrArg F (d.left_inv hw.2).symm
  let J := planeRealJacobian (fderiv ℝ f z)
  have hcross := surfaceTangentCross_coordinate_change heq hY' hf
  have hJ : J ≠ 0 := by
    intro h
    apply surfaceTangentCross_ne_zero_of_injective (hr _ (e.map_source hex)).2
    change _ = J • _ at hcross
    rwa [h,zero_smul] at hcross
  rcases lt_or_gt_of_ne hJ with hj | hj
  · have hsign := (planeChartIndex_spec e d hex hdx).2.unique
      (hasFDerivAt_negative_local_orientation hf.hasFDerivAt hfc hj)
    rw [hsign,← hfx]
    unfold normalizedTangentCross
    rw [hcross,norm_smul,Real.norm_of_nonpos hj.le,smul_smul,smul_smul]
    congr 1
    push_cast
    field_simp
    rfl
  · have hsign := (planeChartIndex_spec e d hex hdx).2.unique
      (hasFDerivAt_positive_local_orientation hf.hasFDerivAt hfc hj)
    rw [hsign,Int.cast_one,one_smul,← hfx]
    exact normalizedTangentCross_compatible heq hY' hf hj

/-- Any independent positive topological atlas fixes a continuous global
surface normal for the given real immersion; no differentiability between
the reference atlas and the original smooth atlas is needed. -/
theorem surface_transverse_field_of_topological_atlas {F : M → Fin 3 → ℝ}
    (e d : M → OpenPartialHomeomorph M ℂ) (he : ∀ x, x ∈ (e x).source) (hd : ∀ x, x ∈ (d x).source)
    (hr : ∀ x, RegularImmersionChart F (e x))
    (hpos : ∀ x y z, z ∈ (d x).source → z ∈ (d y).source → planeChartIndex (d x) (d y) z = 1) :
    ∃ N : M → Fin 3 → ℝ, Continuous N ∧ ∀ x : M,
      surfaceTangentCross (F ∘ (e x).symm) (e x x) ⬝ᵥ N x ≠ 0 := by
  let n := fun x => planeChartIndex (e x) (d x) x
  let Y := fun x => F ∘ (e x).symm
  let N := fun x => (n x:ℝ) • normalizedTangentCross (Y x) (e x x)
  have hn (x : M) : n x = 1 ∨ n x = -1 := (planeChartIndex_spec _ _ (he x) (hd x)).1
  refine ⟨N,continuous_iff_continuousAt.mpr (fun x => ?_),fun x => ?_⟩
  · have hsrc := (e x).map_source (he x)
    have hnc := (normalizedTangentCross_continuousAt ((hr x _ hsrc).1.of_le (by norm_num))
      (hr x _ hsrc).2).comp ((e x).continuousAt (he x))
    apply ((continuousAt_const (y := (n x:ℝ))).smul hnc : ContinuousAt (fun y => (n x:ℝ) • normalizedTangentCross (Y x) (e x y)) x).congr_of_eventuallyEq
    filter_upwards [(e x).open_source.mem_nhds (he x),(d x).open_source.mem_nhds (hd x),
      planeChartIndex_locally_constant (e x) (d x) (he x) (hd x)] with y hey hdy hc
    have ht := planeChartIndex_comp (e y) (d y) (d x) (he y) (hd y) hdy
    rw [hpos y x y (hd y) hdy,one_mul] at ht
    have hs := planeChartIndex_comp (e y) (e x) (d x) (he y) hey hdy
    let u := planeChartIndex (e y) (e x) y
    have heq : n y = n x*u := ht.symm.trans (by rw [hs,hc])
    have hu : u = 1 ∨ u = -1 := (planeChartIndex_spec _ _ (he y) hey).1
    have hunit : n y*u = n x := by rcases hu with h | h <;> simp [heq,h]
    have hreal : (n y:ℝ)*(u:ℝ) = n x := by exact_mod_cast hunit
    change (n y:ℝ) • normalizedTangentCross (Y y) (e y y) = _
    rw [immersion_normal_chartIndex (hr y) (hr x) (he y) hey,smul_smul]
    exact congrArg (· • normalizedTangentCross (Y x) (e x y)) hreal
  · change surfaceTangentCross (Y x) (e x x) ⬝ᵥ ((n x:ℝ) • normalizedTangentCross (Y x) (e x x)) ≠ 0
    rw [dotProduct_smul,smul_eq_mul]
    apply mul_ne_zero
    · rcases hn x with h | h <;> rw [h] <;> norm_num
    · exact (surfaceTangentCross_dot_normalized_pos (hr x _ ((e x).map_source (he x))).2).ne'

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.surface_transverse_field_of_topological_atlas
