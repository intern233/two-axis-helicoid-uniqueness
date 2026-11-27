import TwoAxisHelicoid.HelicoidEndHorizontalRuling
import TwoAxisHelicoid.HelicoidAsymptoticContainment

namespace TwoAxisHelicoid
open Real Set Metric Filter Bornology
open scoped Topology

theorem helicoid_graph_spatial_distance (s : ℝ) (p : ℝ × ℝ) :
    dist (tubeCartesian (helicoidTubeMap ((s,p.1),p.2))) (standardHelicoid p.1 p.2) ≤ |s| := by
  rw [tubeCartesian_normalMap,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs]
  apply mul_le_of_le_one_right (abs_nonneg s)
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
  intro j
  have h := Finset.single_le_sum (f := fun k : Fin 3 => (standardHelicoidNormal p.1 p.2 k)^2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  rw [(standardHelicoid_unit_normal p.1 p.2).1] at h
  rw [Real.norm_eq_abs]
  nlinarith [sq_abs (standardHelicoidNormal p.1 p.2 j),abs_nonneg (standardHelicoidNormal p.1 p.2 j)]

/-- The actual one-sheeted normal graph with decaying height gives both
directions of positional asymptotics, including all points on each end. -/
theorem HasHelicoidC1End.positional_asymptote {M : Type*} [TopologicalSpace M]
    {Y : M → HelicoidTubeCoordinates} (hY : Continuous Y) (hend : HasHelicoidC1End Y) :
    let S := range (tubeCartesian ∘ Y)
    let H := range (fun p : ℝ × ℝ => standardHelicoid p.1 p.2)
    ApproachesSetAtInfinity S H ∧ ApproachesSetAtInfinity H S := by
  obtain ⟨C,_,R,hR,hcompact,E,_,u,_,hgraph,hdecay⟩ := hend
  let D := helicoidProjectedEnd Y C (exteriorPlaneBase R)
  let X := tubeCartesian ∘ Y
  let H := fun p : ℝ × ℝ => standardHelicoid p.1 p.2
  have hx : Continuous X := coordinateTubeHomeomorph.symm.continuous.comp hY
  have hh : Continuous H := by
    apply continuous_pi
    intro j
    fin_cases j <;> simp [H,standardHelicoid] <;> fun_prop
  have hclose (p : exteriorPlaneBase R) : dist (X (E.symm p).1) (H p.1) ≤ |u p| := by
    change dist (tubeCartesian (Y (E.symm p).1)) (standardHelicoid p.1.1 p.1.2) ≤ _
    rw [(hgraph p).2]
    exact helicoid_graph_spatial_distance _ _
  have hsmall (ε : ℝ) (hε : 0 < ε) : ∃ T : ℝ, ∀ p : exteriorPlaneBase R, T ≤ ‖p.1‖ → |u p| < ε := by
    obtain ⟨T,_,hT⟩ := ((hasBasis_cobounded_norm.comap
      (Subtype.val : exteriorPlaneBase R → ℝ × ℝ)).eventually_iff).mp
      (hdecay.eventually (gt_mem_nhds hε))
    exact ⟨T,fun p hp => lt_of_le_of_lt (le_add_of_nonneg_right (Real.sqrt_nonneg _))
      (hT (show p ∈ (Subtype.val : exteriorPlaneBase R → ℝ × ℝ) ⁻¹' {z | T ≤ ‖z‖} from hp))⟩
  obtain ⟨L,hL⟩ := (hcompact.image hx).isBounded.exists_norm_le
  constructor
  · intro ε hε
    obtain ⟨T,hT⟩ := hsmall ε hε
    obtain ⟨B,hB⟩ := ((isCompact_closedBall (0 : ℝ × ℝ) T).image hh).isBounded.exists_norm_le
    refine ⟨max L (B+1)+1,?_⟩
    rintro _ ⟨q,rfl⟩ hnorm
    change max L (B+1)+1 ≤ ‖X q‖ at hnorm
    have hq : q ∈ D := by
      by_contra hn
      have h := hL (X q) ⟨q,hn,rfl⟩
      linarith [le_max_left L (B+1)]
    let p := E ⟨q,hq⟩
    have hc : dist (X q) (H p.1) ≤ |u p| := by simpa only [p,E.symm_apply_apply] using hclose p
    have hp : T ≤ ‖p.1‖ := by
      by_contra! ht
      have hb := hB (H p.1) ⟨p.1,(by simpa [dist_zero_right] using ht.le : p.1 ∈ closedBall 0 T),rfl⟩
      have hn := norm_sub_norm_le (X q) (H p.1)
      rw [← dist_eq_norm] at hn
      linarith [(hgraph p).1,le_max_right L (B+1)]
    exact ⟨H p.1,⟨p.1,rfl⟩,hc.trans_lt (hT p hp)⟩
  · intro ε hε
    obtain ⟨T,hT⟩ := hsmall ε hε
    obtain ⟨B,hB⟩ := ((isCompact_closedBall (0 : ℝ × ℝ) (max R T)).image hh).isBounded.exists_norm_le
    refine ⟨B+1,?_⟩
    rintro _ ⟨p,rfl⟩ hnorm
    change B+1 ≤ ‖H p‖ at hnorm
    have hp : max R T < ‖p‖ := by
      by_contra! ht
      have h := hB (H p) ⟨p,(by simpa [dist_zero_right] using ht : p ∈ closedBall 0 (max R T)),rfl⟩
      linarith
    let w : exteriorPlaneBase R := ⟨p,(le_max_left R T).trans_lt hp⟩
    exact ⟨X (E.symm w).1,⟨(E.symm w).1,rfl⟩,(dist_comm _ _).le.trans_lt
      ((hclose w).trans_lt (hT w ((le_max_right R T).trans hp.le)))⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.HasHelicoidC1End.positional_asymptote
