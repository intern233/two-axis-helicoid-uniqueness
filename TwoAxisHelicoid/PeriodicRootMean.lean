import TwoAxisHelicoid.PeriodicRootStrip
import Mathlib.Analysis.SpecificLimits.Normed

namespace TwoAxisHelicoid
open Complex Set MeasureTheory Filter
open scoped Topology

private theorem continuous_periodic_fourier_mean
    (F : C(AddCircle (1:ℝ),ℂ)) {r M : ℝ} (r0 : 0≤r) (r1 : r<1)
    (positive : ∀ n : ℕ, ‖fourierCoeff F (n:ℤ)‖≤M*r^n)
    (negative : ∀ n : ℕ, ‖fourierCoeff F (-(n:ℤ))‖≤M*r^n) :
    ‖F 0-fourierCoeff F 0‖≤2*(M*r/(1-r)) := by
  let c := fourierCoeff F
  have geom : Summable (fun n : ℕ => M*r^n) :=
    (summable_geometric_of_lt_one r0 r1).mul_left M
  have spos : Summable (fun n : ℕ => c (n:ℤ)) := Summable.of_norm_bounded geom positive
  have sneg : Summable (fun n : ℕ => c (-(n:ℤ))) := Summable.of_norm_bounded geom negative
  have s : Summable c := summable_int_iff_summable_nat_and_neg.mpr ⟨spos,sneg⟩
  have hs0 := has_pointwise_sum_fourier_series_of_summable (f:=F) s 0
  have hs : HasSum c (F 0) := by
    simpa only [fourier_eval_zero,smul_eq_mul,mul_one] using hs0
  have shiftedNeg : Summable (fun n : ℕ => c (-((n+1:ℕ):ℤ))) := (summable_nat_add_iff 1).mpr sneg
  have equality : F 0-c 0=(∑' n : ℕ,c ((n+1:ℕ):ℤ))+(∑' n : ℕ,c (-((n+1:ℕ):ℤ))) := by
    have h := hs.nat_add_neg_add_one.tsum_eq
    simp only [← Nat.cast_add_one] at h
    rw [spos.tsum_add shiftedNeg,spos.tsum_eq_zero_add] at h
    rw [← h]
    simp only [Nat.cast_zero]
    abel
  have upper (v : ℕ → ℂ) (b : ∀ n, ‖v n‖≤M*r^(n+1)) :
      ‖∑' n : ℕ,v n‖≤M*r/(1-r) := by
    have g : Summable (fun n : ℕ => M*r^(n+1)) := (summable_nat_add_iff 1).mpr geom
    have sn := Summable.of_nonneg_of_le (fun n => norm_nonneg (v n)) b g
    apply (norm_tsum_le_tsum_norm sn).trans
    apply (sn.tsum_le_tsum b g).trans
    have eq (n : ℕ) : M*r^(n+1)=(M*r)*r^n := by rw [pow_succ];ring
    simp_rw [eq]
    rw [tsum_mul_left,tsum_geometric_of_lt_one r0 r1,div_eq_mul_inv]
  change ‖F 0-c 0‖≤_
  rw [equality]
  exact (norm_add_le _ _).trans (by linarith [upper _ (fun n => positive (n+1)),upper _ (fun n => negative (n+1))])

/-- A periodic holomorphic strip controls the difference between the
value at the origin and the continuous period average. -/
theorem periodic_strip_mean_error {f : ℂ → ℂ} (per : Function.Periodic f 1)
    {s M : ℝ} (hs : 0<s) (hol : ∀ z : ℂ, |z.im|≤s → DifferentiableAt ℂ f z)
    (lower : ∀ x : ℝ, ‖f ((x:ℂ)+((-s:ℝ):ℂ)*I)‖≤M)
    (upper : ∀ x : ℝ, ‖f ((x:ℂ)+(s:ℂ)*I)‖≤M) :
    let r := Real.exp (-(2*Real.pi*s))
    ‖f 0-(∫ x : ℝ in 0..1, f (x:ℂ))‖≤2*(M*r/(1-r)) := by
  let g := fun x : ℝ => f (x:ℂ)
  have pg : Function.Periodic g 1 := by
    intro x
    simpa only [g,Complex.ofReal_add,Complex.ofReal_one] using per (x:ℂ)
  have cg : Continuous g := continuous_iff_continuousAt.mpr fun x =>
    (hol (x:ℂ) (by simpa only [Complex.ofReal_im,abs_zero] using hs.le)).continuousAt.comp
      Complex.continuous_ofReal.continuousAt
  let F : C(AddCircle (1:ℝ),ℂ) := ⟨pg.lift,continuous_coinduced_dom.mpr cg⟩
  have atReal (x : ℝ) : F (x : AddCircle (1:ℝ))=g x := pg.lift_coe _
  have coefficient (n : ℤ) : fourierCoeff F n=stripFourierCoefficient f n := by
    rw [fourierCoeff_eq_intervalIntegral _ _ 0]
    simp only [one_div,inv_one,one_smul,zero_add,stripFourierCoefficient]
    apply intervalIntegral.integral_congr
    intro x _
    change fourier (-n) (x : AddCircle (1:ℝ)) • F (x : AddCircle (1:ℝ)) =
      Complex.exp (-(n:ℂ)*(2*Real.pi*I)*(x:ℂ))*f (x:ℂ)
    rw [fourier_coe_apply (T:=(1:ℝ)) (n:=-n) (x:=x),atReal]
    simp only [Int.cast_neg,smul_eq_mul,Complex.ofReal_one,div_one,g]
    congr 2
    ring
  let r := Real.exp (-(2*Real.pi*s))
  have hr : r<1 := Real.exp_lt_one_iff.mpr (by have := Real.pi_pos; nlinarith)
  have hneg (z : ℂ) (hz : z.im∈uIcc 0 (-s)) := hol z (by
    rw [uIcc_of_ge (by linarith : -s≤0)] at hz
    exact abs_le.mpr ⟨hz.1,hz.2.trans hs.le⟩)
  have hpos (z : ℂ) (hz : z.im∈uIcc 0 s) := hol z (by
    rw [uIcc_of_le hs.le] at hz
    exact abs_le.mpr ⟨(by linarith [hz.1]),hz.2⟩)
  have pos (n : ℕ) : ‖fourierCoeff F (n:ℤ)‖≤M*r^n := by
    rw [coefficient]
    have h := stripFourierCoefficient_displaced_bound per (n:ℤ) (-s) M hneg lower
    simp only [Int.cast_natCast] at h
    dsimp only [r]
    rw [← Real.exp_nat_mul,mul_comm M]
    convert h using 2
    ring
  have neg (n : ℕ) : ‖fourierCoeff F (-(n:ℤ))‖≤M*r^n := by
    rw [coefficient]
    have h := stripFourierCoefficient_displaced_bound per (-(n:ℤ)) s M hpos upper
    simp only [Int.cast_natCast,Int.cast_neg] at h
    dsimp only [r]
    rw [← Real.exp_nat_mul,mul_comm M]
    convert h using 2
    ring
  have h := continuous_periodic_fourier_mean F (Real.exp_pos _).le hr pos neg
  rw [coefficient] at h
  have hz : F 0=f 0 := by simpa only [g,Complex.ofReal_zero,AddCircle.coe_zero] using atReal 0
  simpa only [hz,stripFourierCoefficient,Int.cast_zero,neg_zero,zero_mul,Complex.exp_zero,one_mul] using h

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.periodic_strip_mean_error
