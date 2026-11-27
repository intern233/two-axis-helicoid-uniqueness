import TwoAxisHelicoid.HolomorphicDiskCover
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.QuadraticDiscriminant

namespace TwoAxisHelicoid
open Complex Metric Set Filter
open scoped Topology ComplexConjugate ContDiff Manifold

/-- Every actual disk biholomorphism has the Möbius form determined
by its value at zero and a unit rotation. -/
theorem disk_automorphism_fraction (f : RiemannUnitDisk ≃ₜ RiemannUnitDisk)
    (hol : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f) (inv : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f.symm) :
    ∃ b k : ℂ, ‖b‖<1 ∧ ‖k‖=1 ∧ ∀ z : RiemannUnitDisk, (f z).1=(k*z.1+b)/(1+conj b*k*z.1) := by
  let o : RiemannUnitDisk := ⟨0,by simp [unitDiskOpen,complexUnitDisk]⟩
  let b := (f o).1
  let F := unitDiskExtension f
  let G := diskMobius b ∘ F
  have hb : b∈complexUnitDisk := (f o).2
  have mapF (z : ℂ) (hz : z∈complexUnitDisk) : F z∈complexUnitDisk := by
    rw [show F z=(f ⟨z,hz⟩).1 from unitDiskExtension_apply f ⟨z,hz⟩]
    exact (f ⟨z,hz⟩).2
  have gnorm (z : ℂ) (hz : z∈complexUnitDisk) : ‖G z‖=‖z‖ := by
    have eq := unitDisk_biholomorphic_distance f hol inv o ⟨z,hz⟩
    change ‖diskMobius b (f ⟨z,hz⟩).1‖=‖diskMobius 0 z‖ at eq
    rw [show G z=diskMobius b (f ⟨z,hz⟩).1 from congrArg (diskMobius b) (unitDiskExtension_apply f ⟨z,hz⟩)]
    simpa [diskMobius] using eq
  have g0 : G 0=0 := norm_eq_zero.mp ((gnorm 0 o.2).trans (norm_zero))
  have diff : DifferentiableOn ℂ G complexUnitDisk := fun z hz =>
    ((diskMobius_analyticAt hb (mapF z hz)).comp (unitDiskExtension_analytic hol z hz)).differentiableAt.differentiableWithinAt
  have maps : MapsTo G complexUnitDisk (closedBall (G 0) 1) := by
    intro z hz
    rw [g0,mem_closedBall,dist_zero_right,gnorm z hz]
    exact (show ‖z‖<1 by simpa only [complexUnitDisk,mem_ball,dist_zero_right] using hz).le
  let w : ℂ := 1/2
  have wn : w≠0 := by norm_num [w]
  have wd : w∈complexUnitDisk := by norm_num [w,complexUnitDisk]
  have full : ‖dslope G 0 w‖=1/1 := by
    rw [dslope_of_ne _ wn,slope_def_module,sub_zero,g0,sub_zero,norm_smul,norm_inv,gnorm w wd,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr wn),div_one]
  obtain ⟨k,hk,linear⟩ := Complex.affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div' diff maps ⟨w,wd,full⟩
  refine ⟨b,k,by simpa only [complexUnitDisk,mem_ball,dist_zero_right] using hb,by simpa using hk,?_⟩
  intro z
  have eq : G z.1=k*z.1 := by simpa only [g0,zero_add,sub_zero,smul_eq_mul,mul_comm] using linear z.2
  have back := diskMobius_inverse hb (mapF z.1 z.2)
  change diskMobius (-b) (G z.1)=F z.1 at back
  rw [eq,show F z.1=(f z).1 from unitDiskExtension_apply f z] at back
  simpa only [diskMobius,sub_neg_eq_add,map_neg,neg_mul,← mul_assoc] using back.symm

/-- A fixed-point-free disk generator fixes a point on the unit circle.
The two roots of its fixed-point equation have product of norm one. -/
theorem fixed_point_free_disk_boundary_root {b k : ℂ} (hb : ‖b‖<1) (hk : ‖k‖=1)
    (free : ∀ z : ℂ, ‖z‖<1 → (k*z+b)/(1+conj b*k*z)≠z) :
    ∃ u : ℂ, ‖u‖=1 ∧ k*u+b=u*(1+conj b*k*u) := by
  have nb : b≠0 := by intro h; exact free 0 (by simp) (by simp [h])
  have nk : k≠0 := norm_ne_zero_iff.mp (hk.trans_ne one_ne_zero)
  let a := conj b*k
  have na : a≠0 := mul_ne_zero (by simpa using nb) nk
  let B := 1-k
  obtain ⟨s,hs⟩ := IsAlgClosed.exists_pow_nat_eq (B^2+4*a*b) (by decide : 0<2)
  let u := (-B+s)/(2*a)
  let v := (-B-s)/(2*a)
  have root (w : ℂ) (hw : w=u ∨ w=v) : k*w+b=w*(1+a*w) := by
    have disc : discrim a B (-b)=s*s := by rw [← sq,hs]; simp [discrim]
    have z := (quadratic_eq_zero_iff na disc w).mpr hw
    dsimp [B] at z
    linear_combination -z
  have product : u*v= -b/a := by
    have num : (-B+s)*(-B-s)= -4*a*b := by linear_combination -hs
    change ((-B+s)/(2*a))*((-B-s)/(2*a))= -b/a
    rw [div_mul_div_comm,num]
    field_simp [na]
    ring
  have outer (w : ℂ) (h : w=u ∨ w=v) : 1≤‖w‖ := by
    by_contra! small
    have den : 1+a*w≠0 := by
      have h : ‖a*w‖<1 := by
        rw [norm_mul,show ‖a‖=‖b‖ from by simp [a,hk]]
        exact (mul_le_mul_of_nonneg_right hb.le (norm_nonneg _)).trans_lt (by simpa using small)
      intro neg
      have he : a*w= -1 := by linear_combination neg
      rw [he,norm_neg,norm_one] at h
      exact lt_irrefl _ h
    exact free w small ((div_eq_iff den).mpr (root w h))
  have size := congrArg norm product
  change ‖u*v‖=‖-b/a‖ at size
  rw [norm_mul,show ‖-b/a‖=1 from by rw [norm_div,norm_neg,show ‖a‖=‖b‖ from by simp [a,hk],div_self (norm_ne_zero_iff.mpr nb)]] at size
  have lo := outer u (Or.inl rfl)
  have hi := outer v (Or.inr rfl)
  exact ⟨u,le_antisymm (by nlinarith [mul_nonneg (norm_nonneg u) (sub_nonneg.mpr hi)]) lo,root u (Or.inl rfl)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.fixed_point_free_disk_boundary_root
