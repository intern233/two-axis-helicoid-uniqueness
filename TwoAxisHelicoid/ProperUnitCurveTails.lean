import TwoAxisHelicoid.ThinCurveProjection
import Mathlib.Topology.Maps.Proper.Basic

namespace TwoAxisHelicoid
open Real Set Metric

theorem tubeCoordinates_norm_le_of_sum_sq_le_one (v : HelicoidTubeCoordinates)
    (hv : (∑ i, (tubeCartesian v i)^2) ≤ 1) : ‖v‖ ≤ 1 := by
  have hi (i : Fin 3) : (tubeCartesian v i)^2 ≤ 1 :=
    (Finset.single_le_sum (fun j _ => sq_nonneg (tubeCartesian v j)) (Finset.mem_univ i)).trans hv
  have ha (i : Fin 3) : |tubeCartesian v i| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> nlinarith [hi i]
  simp only [Prod.norm_def,Real.norm_eq_abs,max_le_iff]
  exact ⟨⟨ha 0,ha 1⟩,ha 2⟩

/-- Properness lets one enlarge a compact core so that every unit-speed
surface curve segment of length at most one remains outside the old core. -/
theorem proper_surface_unit_curve_avoids_core {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} (hp : IsProperMap X)
    {K : Set M} (hK : IsCompact K) :
    ∃ L : Set M, IsCompact L ∧ ∀ q ∉ L, ∀ γ : ℝ → M, ∀ v : ℝ → HelicoidTubeCoordinates,
      γ 0 = q →
      (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (X ∘ γ) (v t) t) →
      (∀ t ∈ Icc (0 : ℝ) 1, (∑ i, (tubeCartesian (v t) i)^2) ≤ 1) →
      ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ K := by
  obtain ⟨C,hC0,hC⟩ := (hK.image hp.continuous).isBounded.exists_pos_norm_le
  let L := X ⁻¹' closedBall 0 (C+2)
  refine ⟨L,hp.isCompact_preimage (isCompact_closedBall 0 (C+2)),?_⟩
  intro q hq γ v hγ hd hv t ht hKγ
  have hlarge : C+2 < ‖X q‖ := by
    simpa only [L,mem_preimage,mem_closedBall,dist_zero_right,not_le] using hq
  have hdist := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s hs => (hd s hs).hasDerivWithinAt)
    (fun s hs => tubeCoordinates_norm_le_of_sum_sq_le_one (v s) (hv s (Ico_subset_Icc_self hs))) t ht
  simp only [one_mul,sub_zero,Function.comp_apply,hγ] at hdist
  have hsmall := hC (X (γ t)) ⟨γ t,hKγ,rfl⟩
  have hnorm : ‖X q‖ ≤ ‖X (γ t)‖+‖X (γ t)-X q‖ := by
    calc
      ‖X q‖ = ‖X (γ t)-(X (γ t)-X q)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  linarith [ht.2]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.proper_surface_unit_curve_avoids_core
