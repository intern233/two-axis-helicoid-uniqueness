import TwoAxisHelicoid.ExteriorGraphCutoff
import TwoAxisHelicoid.SmoothFiberCutoff
import TwoAxisHelicoid.HelicoidAmbientDiffeomorph
import TwoAxisHelicoid.HelicoidProjectionBound

namespace TwoAxisHelicoid
open Set Filter Bornology
open scoped Topology ContDiff
set_option maxHeartbeats 1000000

/-- Smoothly straighten a genuinely decaying normal graph while fixing
any prescribed compact subset of ambient space pointwise. Every time
slice and its inverse are smooth; both vary jointly continuously. The
cutoff, its derivative bound, and the small global graph extension are
constructed from the supplied exterior height function. -/
theorem exterior_helicoid_graph_ambient_straightening {R : ℝ}
    {u : exteriorPlaneBase R → ℝ}
    (hus : ContDiffOn ℝ (∞ : WithTop ℕ∞) (extendOpenScalar u) (exteriorPlaneBase R))
    (hu : Tendsto (fun p => |u p|)
      (comap (Subtype.val : exteriorPlaneBase R → ℝ × ℝ) (cobounded (ℝ × ℝ))) (𝓝 0))
    {K : Set HelicoidTubeCoordinates} (hK : IsCompact K) :
    ∃ (B : ℝ) (Ψ : Icc (0 : ℝ) 1 → HelicoidTubeCoordinates ≃ₜ HelicoidTubeCoordinates),
      R < B ∧ 0 < B ∧
      Continuous (fun q : Icc (0 : ℝ) 1 × HelicoidTubeCoordinates => Ψ q.1 q.2) ∧
      Continuous (fun q : Icc (0 : ℝ) 1 × HelicoidTubeCoordinates => (Ψ q.1).symm q.2) ∧
      (∀ time, ContDiff ℝ (∞ : WithTop ℕ∞) (Ψ time) ∧
        ContDiff ℝ (∞ : WithTop ℕ∞) (Ψ time).symm) ∧
      Ψ ⟨0,by norm_num⟩ = Homeomorph.refl HelicoidTubeCoordinates ∧
      (∀ time y, y ∈ K → Ψ time y = y) ∧
      (∀ p : exteriorPlaneBase R, B ≤ ‖p.1‖ →
        Ψ ⟨1,by norm_num⟩ (helicoidTubeMap ((0,p.1.1),p.1.2)) =
          helicoidTubeMap ((u p,p.1.1),p.1.2) ∧
        (Ψ ⟨1,by norm_num⟩).symm (helicoidTubeMap ((u p,p.1.1),p.1.2)) =
          helicoidTubeMap ((0,p.1.1),p.1.2)) := by
  obtain ⟨C,δ,hC,hδ,_hδsize,hsmall,hχ⟩ := normalStraighteningCutoff_small_graph_size
  obtain ⟨L,hL⟩ := hK.isBounded.exists_norm_le
  obtain ⟨v,B,hB0,hBR,hBA,hvs,hvbound,hvzero,hvfar⟩ :=
    exterior_graph_smooth_small_cutoff hus hu (2*L+1) hδ
  let Ψ : Icc (0 : ℝ) 1 → HelicoidTubeCoordinates ≃ₜ HelicoidTubeCoordinates :=
    fun time => helicoidAmbientIsotopy hχ hvs.continuous hvbound hsmall time.2
  refine ⟨B+1,Ψ,by linarith,by linarith,
    helicoidAmbientIsotopy_joint_continuous hχ hvs.continuous hvbound hsmall,
    helicoidAmbientIsotopy_inverse_joint_continuous hχ hvs.continuous hvbound hsmall,
    ?_,helicoidAmbientIsotopy_time_zero hχ hvs.continuous hvbound hsmall,?_,?_⟩
  · intro time
    exact helicoidAmbientIsotopy_smooth hχ normalStraighteningCutoff_contDiff hvs hvbound hsmall time.2
  · intro time y hyK
    by_cases hy : y ∈ helicoidFiberChart.target
    · have hb : ‖(helicoidFiberChart.symm y).2‖ ≤ B := by
        change ‖helicoidBaseCoordinates y‖ ≤ B
        have hh := helicoidBaseCoordinates_norm_bound hy
        have hhK := hL y hyK
        linarith
      have hv := hvzero (helicoidFiberChart.symm y).2 hb
      rw [helicoidAmbientIsotopy_apply_in_tube hχ hvs.continuous hvbound hsmall time.2 hy]
      have hfixed := normalFiberHomeomorph_fixes_zero_height hχ hvs.continuous hvbound hsmall
        time.2 hv (helicoidFiberChart.symm y).1
      rw [Prod.mk.eta] at hfixed
      rw [hfixed,helicoidFiberChart.right_inv hy]
    · exact extendPartialMap_of_not_mem _ hy
  · intro p hp
    have h := helicoidAmbientIsotopy_time_one_graph hχ hvs.continuous hvbound hsmall p.1
    rw [hvfar p hp] at h
    refine ⟨h,?_⟩
    rw [← h]
    exact (Ψ ⟨1,by norm_num⟩).symm_apply_apply _

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.exterior_helicoid_graph_ambient_straightening
