import TwoAxisHelicoid.CertifiedWeierstrassSeparation
import TwoAxisHelicoid.ComplexBallChecked

namespace TwoAxisHelicoid
open Complex ComplexBall Set Metric

/-- Uniform rational coefficient disks with a margin for the first
real derivative certify injectivity on the entire projected disk. -/
theorem certified_disk_injective_of_coefficient_margins (b : ComplexBall) (v : Fin 3 → ComplexBall) (ε l : ℚ)
    (rad : 0≤b.radius) (ep : 0≤ε) (lp : 0≤l) (strict : 3*ε^2<l^2)
    (width : ∀ j, 2*(v j).radius≤ε) (negative : (v 0).center.re+(v 0).radius≤ -l)
    (spec : ∀ {w}, w∈closedBall b.center.val (b.radius:ℝ) → w∉certifiedPeriodPair.lattice ∧
      ∀ j, (v j).Contains (coordinateData certifiedClosedParameters.t certifiedClosedParameters.a 1 certifiedClosedParameters.height_pos w j)) :
    InjOn certifiedTorusImmersion (puncturedPlaneProjection certifiedPeriodPair ''
      (Subtype.val ⁻¹' closedBall b.center.val (b.radius:ℝ))) := by
  let p := certifiedClosedParameters
  let f := coordinateData p.t p.a 1 p.height_pos
  let U := closedBall b.center.val (b.radius:ℝ)
  have center := spec (mem_closedBall_self (by exact_mod_cast rad))
  let a := f b.center.val
  have err (z : ℂ) (hz : z∈U) (j : Fin 3) : ‖f z j-a j‖≤(ε:ℝ) := by
    have hh := dist_triangle (f z j) (v j).center.val (a j)
    simp only [dist_eq_norm] at hh
    rw [norm_sub_rev (v j).center.val] at hh
    have bw : 2*((v j).radius:ℝ)≤(ε:ℝ) := by exact_mod_cast width j
    have h₀ := (spec hz).2 j
    have h₁ := center.2 j
    change ‖f z j-(v j).center.val‖≤_ at h₀
    change ‖a j-(v j).center.val‖≤_ at h₁
    linarith
  have n : (a 0).re≤ -(l:ℝ) := (re_bounds (center.2 0)).2.trans (by exact_mod_cast negative)
  have lnon : 0≤(l:ℝ) := by exact_mod_cast lp
  have lo := (sq_le_sq₀ lnon (show 0≤ -(a 0).re by linarith)).mpr (by linarith : (l:ℝ)≤ -(a 0).re)
  have st : 3*(ε:ℝ)^2<(l:ℝ)^2 := by exact_mod_cast strict
  apply certified_projected_box_injective (convex_closedBall _ _) (fun _ h => (spec h).1)
    (coordinateData_null p.height_pos p.abscissa_mem center.1) (by exact_mod_cast ep) err
  change 3*(ε:ℝ)^2<(a 0).re^2+(a 1).re^2+(a 2).re^2
  nlinarith [sq_nonneg (a 1).re,sq_nonneg (a 2).re]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_disk_injective_of_coefficient_margins
