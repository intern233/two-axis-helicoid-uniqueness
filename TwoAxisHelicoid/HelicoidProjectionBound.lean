import TwoAxisHelicoid.HelicoidProjectionProper
import Mathlib.Analysis.Normed.Group.Bounded

namespace TwoAxisHelicoid
open Real Set Bornology

theorem helicoidAngle_abs_le {r s : ℝ} (hs : |s| ≤ 1) : |helicoidAngle r s| ≤ 1 := by
  have hr : |r| ≤ helicoidQ r := by
    nlinarith [helicoidQ_sq r,helicoidQ_pos r,sq_abs r]
  rw [helicoidAngle,abs_div,abs_mul,abs_of_pos (helicoidQ_pos r)]
  apply (div_le_iff₀ (helicoidQ_pos r)).mpr
  simpa only [one_mul] using mul_le_mul hs hr (abs_nonneg r) zero_le_one

/-- Actual normal coordinates cannot grow on a bounded spatial set. The
estimate is uniform over the entire width-one strip. -/
theorem helicoid_normal_parameters_norm_bound (r θ s : ℝ) (hs : |s| ≤ 1) :
    ‖(r,θ)‖ ≤ 2*‖helicoidTubeMap ((s,r),θ)‖+1 := by
  let y := helicoidTubeMap ((s,r),θ)
  have hpolar : r = y.1.1*cos θ+y.1.2*sin θ := by
    dsimp [y,helicoidTubeMap,helicoidNormalMap]
    calc
      r = r*(sin θ^2+cos θ^2) := by rw [sin_sq_add_cos_sq,mul_one]
      _ = _ := by ring
  have hx : |y.1.1| ≤ ‖y‖ := by
    simpa only [Real.norm_eq_abs] using (norm_fst_le y.1).trans (norm_fst_le y)
  have hy : |y.1.2| ≤ ‖y‖ := by
    simpa only [Real.norm_eq_abs] using (norm_snd_le y.1).trans (norm_fst_le y)
  have hz : |y.2| ≤ ‖y‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le y
  have hr : |r| ≤ 2*‖y‖ := by
    calc
      |r| = |y.1.1*cos θ+y.1.2*sin θ| := congrArg abs hpolar
      _ ≤ |y.1.1*cos θ|+|y.1.2*sin θ| := abs_add_le _ _
      _ ≤ |y.1.1|+|y.1.2| := by
        rw [abs_mul,abs_mul]
        nlinarith [abs_cos_le_one θ,abs_sin_le_one θ,abs_nonneg y.1.1,abs_nonneg y.1.2]
      _ ≤ _ := by linarith
  have hθ : |θ| ≤ ‖y‖+1 := by
    have he : θ = y.2-helicoidAngle r s := by
      dsimp [y,helicoidTubeMap,helicoidNormalMap]
      ring
    calc
      |θ| = |y.2-helicoidAngle r s| := congrArg abs he
      _ ≤ |y.2|+|helicoidAngle r s| := abs_sub _ _
      _ ≤ _ := add_le_add hz (helicoidAngle_abs_le hs)
  rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
  exact max_le (by linarith) (by nlinarith [norm_nonneg y])

theorem helicoidBaseCoordinates_norm_bound {y : HelicoidTubeCoordinates}
    (hy : y ∈ helicoidTubeEquiv.target) :
    ‖helicoidBaseCoordinates y‖ ≤ 2*‖y‖+1 := by
  have hs : |(helicoidTubeEquiv.symm y).1.1| < 1 := helicoidTubeEquiv.map_target hy
  have h := helicoid_normal_parameters_norm_bound (helicoidTubeEquiv.symm y).1.2
    (helicoidTubeEquiv.symm y).2 (helicoidTubeEquiv.symm y).1.1 hs.le
  change ‖helicoidBaseCoordinates y‖ ≤ 2*‖helicoidTubeMap (helicoidTubeEquiv.symm y)‖+1 at h
  have he : helicoidTubeMap (helicoidTubeEquiv.symm y) = y := helicoidTubeEquiv.right_inv hy
  rwa [he] at h

theorem helicoidBaseCoordinates_image_bounded {A : Set HelicoidTubeCoordinates}
    (hA : IsBounded A) (hTube : A ⊆ helicoidTubeEquiv.target) :
    IsBounded (helicoidBaseCoordinates '' A) := by
  obtain ⟨C,hC⟩ := hA.exists_norm_le
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨2*C+1,?_⟩
  rintro q ⟨y,hy,rfl⟩
  exact (helicoidBaseCoordinates_norm_bound (hTube hy)).trans (by linarith [hC y hy])

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoidBaseCoordinates_image_bounded
