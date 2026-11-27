import TwoAxisHelicoid.OriginalPeriodRegularity
import TwoAxisHelicoid.DescendingThetaQuasiperiod
import TwoAxisHelicoid.WeierstrassSecondOrder

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
open scoped Interval

private theorem descending_period_mem {t : ℝ} (ht : 0 < t) :
    1-I*t ∈ (rhombicPeriodPair t ht).lattice := by
  have h := (rhombicPeriodPair t ht).lattice.sub_mem
    (rhombicPeriodPair t ht).ω₁_mem_lattice (rhombicPeriodPair t ht).ω₂_mem_lattice
  change (2:ℂ)-(1+I*t) ∈ _ at h
  rwa [show (2:ℂ)-(1+I*t) = 1-I*t by ring] at h

/-- Quasiperiod of the logarithmic theta derivative for the actual descending
generator. The starting point is arbitrary away from the lattice. -/
theorem thetaW_add_descending_generator {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    thetaW t (z+(1-I*t)) = thetaW t z+(Real.pi : ℂ)*I :=
  thetaW_descending_quasiperiod ht hz

/-- The full complex second moment on the manuscript's sloping path, with its
orientation and the length of its complex period. -/
theorem sloping_weierstrass_square_integral {t : ℝ} (ht : 0 < t) :
    slopingIntegral t (fun w => ((rhombicPeriodPair t ht).weierstrassP w)^2) =
      (rhombicPeriodPair t ht).g₂/12*(1-I*t) := by
  let L := rhombicPeriodPair t ht
  let z := originalPeriodPath t
  let q : ℂ := (1-I*t)/2
  have regular {s : ℝ} (hs : s ∈ Icc (-1:ℝ) 1) : z s ∉ L.lattice :=
    rhombic_open_rectangle_not_mem ht (originalPeriodPath_mem_rectangle ht hs)
  have hz : Continuous z := continuous_iff_continuousAt.mpr fun s => (originalPeriodPath_hasDerivAt t s).continuousAt
  have square : ContinuousOn (fun s => (L.weierstrassP (z s))^2) (Icc (-1:ℝ) 1) := by
    intro s hs
    exact (((L.analyticOnNhd_weierstrassP _ (regular hs)).continuousAt.comp
      (hz.continuousAt)).pow 2).continuousWithinAt
  have integ := square.intervalIntegrable_of_Icc (by norm_num : (-1:ℝ) ≤ 1) (μ := volume)
  have hd (s : ℝ) (hs : s ∈ uIcc (-1:ℝ) 1) :
      HasDerivAt (fun u : ℝ => L.derivWeierstrassP (z u))
        (q*(6*(L.weierstrassP (z s))^2-L.g₂/2)) s := by
    have reg := regular (s:=s) (by simpa only [uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] using hs)
    have hp := (L.analyticOnNhd_derivWeierstrassP _ reg).differentiableAt.hasDerivAt
    rw [rhombic_weierstrass_second_order ht reg] at hp
    simpa only [Function.comp_def,mul_comm] using hp.comp s (originalPeriodPath_hasDerivAt t s)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((integ.const_mul 6).sub intervalIntegrable_const).const_mul q)
  have hp := L.derivWeierstrassP_add_coe (z (-1)) ⟨1-I*t,descending_period_mem ht⟩
  have ep : z (-1)+(⟨1-I*t,descending_period_mem ht⟩ : L.lattice) = z 1 := by
    change originalPeriodPath t (-1)+(1-I*t) = originalPeriodPath t 1
    unfold originalPeriodPath
    push_cast
    ring
  rw [ep] at hp
  rw [hp,sub_self,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (integ.const_mul 6) intervalIntegrable_const,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const] at hi
  change q*(∫ s : ℝ in (-1)..1, L.weierstrassP (z s)^2) = L.g₂/12*(1-I*t)
  have twice : (1 - (-1) : ℝ) = 2 := by norm_num
  simp only [Complex.real_smul,twice,Complex.ofReal_ofNat] at hi
  dsimp only [q] at hi ⊢
  linear_combination (1/6:ℂ)*hi

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaW_add_descending_generator
#print axioms TwoAxisHelicoid.sloping_weierstrass_square_integral
