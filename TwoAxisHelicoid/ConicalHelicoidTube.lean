import TwoAxisHelicoid.HelicoidGlobalTube
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace TwoAxisHelicoid
open Real Set Metric

/-- A narrow horizontal angular cone lies close to the helicoid: change
the height by the small angular displacement while keeping the horizontal
point fixed. The bound is independent of the horizontal radius. -/
theorem horizontal_cone_helicoid_distance {r t θ κ : ℝ} (hκ : 0 ≤ κ)
    (hcone : |t| ≤ κ*|r|) :
    ∃ ρ φ : ℝ, helicoidSquaredDistance
      (r*cos θ-t*sin θ,r*sin θ+t*cos θ,θ) ρ φ ≤ κ^2 := by
  by_cases hr : r = 0
  · have ht : t = 0 := abs_eq_zero.mp (le_antisymm (by simpa [hr] using hcone) (abs_nonneg t))
    subst r
    subst t
    refine ⟨0,θ,?_⟩
    simpa [helicoidSquaredDistance] using sq_nonneg κ
  · let β := arctan (t/r)
    let ρ := r/cos β
    have hc : cos β ≠ 0 := (cos_arctan_pos (t/r)).ne'
    have hs : sin β = (t/r)*cos β := by
      apply (div_eq_iff hc).mp
      simpa only [tan_eq_sin_div_cos] using tan_arctan (t/r)
    have hx : r*cos θ-t*sin θ = ρ*cos (θ+β) := by
      rw [cos_add,hs]
      dsimp [ρ]
      field_simp
    have hy : r*sin θ+t*cos θ = ρ*sin (θ+β) := by
      rw [sin_add,hs]
      dsimp [ρ]
      field_simp
    have hb : |β| ≤ κ := by
      calc |β| ≤ |t/r| := abs_arctan_le_abs
           _ = |t|/|r| := abs_div _ _
           _ ≤ κ := (div_le_iff₀ (abs_pos.mpr hr)).mpr (by simpa only [mul_comm] using hcone)
    refine ⟨ρ,θ+β,?_⟩
    have he : helicoidSquaredDistance
        (r*cos θ-t*sin θ,r*sin θ+t*cos θ,θ) ρ (θ+β) = β^2 := by
      unfold helicoidSquaredDistance
      dsimp only
      rw [hx,hy]
      ring
    rw [he]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg β) hκ).mpr hb

theorem helicoid_tube_of_squared_distance_le {y : HelicoidTubeCoordinates} {κ : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ < 1)
    (hnear : ∃ r θ : ℝ, helicoidSquaredDistance (y.1.1,y.1.2,y.2) r θ ≤ κ^2) :
    y ∈ helicoidTubeEquiv.target ∧ |helicoidSignedDistance y| ≤ κ := by
  obtain ⟨r,θ,hd⟩ := hnear
  rw [helicoidSquaredDistance_eq_euclidean_dist] at hd
  have hd' := (sq_le_sq₀ dist_nonneg hκ0).mp hd
  have hi : infDist (helicoidEuclideanPoint (y.1.1,y.1.2,y.2)) euclideanHelicoidSet ≤ κ :=
    (infDist_le_dist_of_mem (show euclideanHelicoid r θ ∈ euclideanHelicoidSet from ⟨r,θ,rfl⟩)).trans hd'
  have ht := helicoidTubeEquiv_target_iff_distance.mpr (hi.trans_lt hκ)
  exact ⟨ht,by rwa [helicoidSignedDistance_abs_eq_infDist ht]⟩

theorem horizontal_cone_in_helicoid_tube {r t θ κ : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ < 1)
    (hcone : |t| ≤ κ*|r|) :
    ((r*cos θ-t*sin θ,r*sin θ+t*cos θ),θ) ∈ helicoidTubeEquiv.target ∧
      |helicoidSignedDistance ((r*cos θ-t*sin θ,r*sin θ+t*cos θ),θ)| ≤ κ :=
  helicoid_tube_of_squared_distance_le hκ0 hκ (horizontal_cone_helicoid_distance hκ0 hcone)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.horizontal_cone_in_helicoid_tube
