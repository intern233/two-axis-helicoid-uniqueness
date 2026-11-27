import TwoAxisHelicoid.WeierstrassSecondOrder
import TwoAxisHelicoid.HorizontalRightValue

namespace TwoAxisHelicoid
open Complex Set MeasureTheory

theorem weierstrass_midline_square_integral {t : ℝ} (ht : 0 < t) :
    (∫ x : ℝ in (-1)..1, (rhombicPeriodPair t ht).weierstrassP ((x:ℂ)+I*((t/2:ℝ):ℂ))^2) =
      (rhombicPeriodPair t ht).g₂/6 := by
  let L := rhombicPeriodPair t ht
  let z := fun x : ℝ => (x:ℂ)+I*((t/2:ℝ):ℂ)
  have hc : Continuous (fun x : ℝ => L.weierstrassP (z x)^2) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact ((rhombic_weierstrassP_hasDerivAt ht (rhombic_midline_not_mem ht x)).continuousAt.comp
      (f := z) (by fun_prop)).pow 2
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => L.derivWeierstrassP (z y))
      (6*L.weierstrassP (z x)^2-L.g₂/2) x := by
    have hh := (L.analyticOnNhd_derivWeierstrassP _ (rhombic_midline_not_mem ht x)).differentiableAt.hasDerivAt
    rw [rhombic_weierstrass_second_order ht (rhombic_midline_not_mem ht x)] at hh
    have harg : HasDerivAt z 1 x := by simpa [z] using (hasDerivAt_id x).ofReal_comp.add_const (I*((t/2:ℝ):ℂ))
    simpa only [Function.comp_def,mul_one] using hh.comp x harg
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((hc.intervalIntegrable (-1) 1 (μ := volume)).const_mul 6 |>.sub intervalIntegrable_const)
  have htwo : (2:ℂ) ∈ L.lattice := by
    apply PeriodPair.mem_lattice.mpr
    refine ⟨1,0,?_⟩
    simp [L,rhombicPeriodPair]
  have hp := L.derivWeierstrassP_add_coe (z (-1)) ⟨2,htwo⟩
  have he : z (-1)+(⟨2,htwo⟩:L.lattice) = z 1 := by simp [z]; ring
  rw [he] at hp
  rw [hp,sub_self] at hi
  rw [intervalIntegral.integral_sub ((hc.intervalIntegrable (-1) 1).const_mul 6) intervalIntegrable_const,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const] at hi
  norm_num only [sub_neg_eq_add,Complex.real_smul,Complex.ofReal_ofNat] at hi
  change (∫ x : ℝ in (-1)..1, L.weierstrassP (z x)^2) = L.g₂/6
  linear_combination (1/6:ℂ)*hi

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.weierstrass_midline_square_integral
