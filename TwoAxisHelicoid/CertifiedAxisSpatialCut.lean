import TwoAxisHelicoid.CertifiedFirstSpatialDisk
import TwoAxisHelicoid.WeierstrassChordError
import TwoAxisHelicoid.FiniteSpatialSeparationCover
import TwoAxisHelicoid.CenteredActualImmersion

namespace TwoAxisHelicoid
open Complex ComplexBall Set Metric

private theorem first_horizontal_coarse_ball :
    (⟨⟨-5/2,0⟩,1/4⟩ : ComplexBall).coarsens (firstSpatialFormBall 0) := by decide +kernel

/-- The actual first spatial coordinate on the disk is close to the
explicit affine function with slope -5/2. -/
theorem certified_horizontal_chord_at_one {z : ℂ} (hz : z∈closedBall (1:ℂ) (1/1000:ℝ)) :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    |X z 0-X 1 0+(5/2)*(z.re-1)| ≤ (1/4)*‖z-1‖ := by
  let p := certifiedClosedParameters
  let X := actualGlobalImmersion p.t p.a 1 p.height_pos
  let b : ComplexBall := ⟨⟨-5/2,0⟩,1/4⟩
  have h := actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
    p.vertical_closed p.horizontal_closed
  have eq := weierstrass_coordinate_chord_error (X := X) (convex_closedBall (1:ℂ) (1/1000:ℝ))
    (fun w hw => (h.2.2.2 w (certified_first_spatial_disk_coefficients hw).1).1) 0 b
    (fun _ hw => coarsen_contains ((certified_first_spatial_disk_coefficients hw).2 0) first_horizontal_coarse_ball)
    (mem_closedBall_self (by norm_num)) hz
  have model : ((z-1)*b.center.val).re= -(5/2)*(z.re-1) := by
    norm_num [b,QComplex.val,Complex.mul_re]
    ring
  rw [model] at eq
  simpa only [neg_mul,sub_neg_eq_add,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,b] using eq

private theorem first_subdisk_bounds {z : ℂ} {c : ℝ} (offset : |c-1|≤1/2000)
    (inside : z∈closedBall (c:ℂ) (1/10000:ℝ)) :
    z∈closedBall (1:ℂ) (1/1000:ℝ) ∧ ‖z-1‖≤3/5000 ∧ |z.re-c|≤1/10000 := by
  have d := mem_closedBall.mp inside
  have dist_one : dist (c:ℂ) 1=|c-1| := by
    change dist ((c:ℝ):ℂ) ((1:ℝ):ℂ)=_
    rw [Complex.isometry_ofReal.dist_eq,Real.dist_eq]
  have h := dist_triangle z (c:ℂ) 1
  rw [dist_one] at h
  have small : dist z 1≤3/5000 := by linarith
  have re := (abs_re_le_norm (z-(c:ℂ))).trans (show ‖z-(c:ℂ)‖≤1/10000 from (dist_eq_norm z (c:ℂ)) ▸ d)
  exact ⟨mem_closedBall.mpr (by linarith), (dist_eq_norm z (1:ℂ)) ▸ small,by simpa only [sub_re,ofReal_re] using re⟩

/-- Two full rational parameter disks are strictly separated by the
centered physical plane x₁=0. The coordinate gap between them is at
least 1/625, uniformly for every pair of their points. -/
theorem certified_two_axis_disks_coordinate_gap {u v : ℂ}
    (left : u∈closedBall ((1-1/2000:ℝ):ℂ) (1/10000:ℝ))
    (right : v∈closedBall ((1+1/2000:ℝ):ℂ) (1/10000:ℝ)) :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    1/1250≤X u 0-X 1 0 ∧ X v 0-X 1 0≤ -(1/1250) ∧ 1/625≤X u 0-X v 0 := by
  obtain ⟨ul,us,ur⟩ := first_subdisk_bounds (by norm_num) left
  obtain ⟨vl,vs,vr⟩ := first_subdisk_bounds (by norm_num) right
  have upper_left := (abs_le.mp ur).2
  have lower_right := (abs_le.mp vr).1
  have low := (abs_le.mp (certified_horizontal_chord_at_one ul)).1
  have high := (abs_le.mp (certified_horizontal_chord_at_one vl)).2
  dsimp only
  constructor
  · linarith
  constructor <;> linarith

theorem certified_projected_axis_disk_rational_cut :
    let p := certifiedClosedParameters
    let F := centeredActualTorusImmersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
      p.vertical_closed p.horizontal_closed
    let box := fun c : ℝ => puncturedPlaneProjection certifiedPeriodPair '' (Subtype.val ⁻¹' closedBall (c:ℂ) (1/10000:ℝ))
    RationalCoordinateCut F (box (1+1/2000)) (box (1-1/2000)) := by
  refine ⟨0,0,?_,?_⟩
  · rintro _ ⟨v,hv,rfl⟩
    have g := (certified_two_axis_disks_coordinate_gap (mem_closedBall_self (by norm_num)) hv).2.1
    change _-_<((0:ℚ):ℝ)
    exact lt_of_le_of_lt g (by norm_num)
  · rintro _ ⟨u,hu,rfl⟩
    have g := (certified_two_axis_disks_coordinate_gap hu (mem_closedBall_self (by norm_num))).1
    change ((0:ℚ):ℝ)<_-_
    exact lt_of_lt_of_le (by norm_num) g

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_horizontal_chord_at_one
#print axioms TwoAxisHelicoid.certified_two_axis_disks_coordinate_gap
#print axioms TwoAxisHelicoid.certified_projected_axis_disk_rational_cut
