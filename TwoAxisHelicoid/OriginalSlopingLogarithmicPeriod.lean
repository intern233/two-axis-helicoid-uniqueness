import TwoAxisHelicoid.EllipticKernelTotalHeat
import TwoAxisHelicoid.OriginalSigmaPeriodDerivative

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
open scoped Interval

/-- The Rₐ-weighted integral in Appendix A.2 is taken along the descending
generator with the manuscript's sigma kernel, without taking real parts. -/
theorem original_sloping_logarithmic_period {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0:ℝ) 1) :
    let L := rhombicPeriodPair t ht
    slopingIntegral t (fun z => ellipticKernelRa t ht a z*thetaSigmaKernel t a z) =
      2*thetaW t a*originalSigmaPeriod t a+
        2*((a:ℂ)-1)*slopingIntegral t
          (fun z => (L.weierstrassP z+thetaEtaExpression t)*thetaSigmaKernel t a z) := by
  let L := rhombicPeriodPair t ht
  let z := originalPeriodPath t
  let A := thetaA t a
  let eta := thetaEtaExpression t
  let q : ℂ := (1-I*t)/2
  have ha2 : a ∈ Ioo (0:ℝ) 2 := ⟨ha.1,by linarith [ha.2]⟩
  have pole := real_not_mem_rhombic_lattice_of_pos ht ha2.1 ha2.2
  have regular {s : ℝ} (hs : s ∈ Icc (-1:ℝ) 1) : z s ∉ L.lattice :=
    rhombic_open_rectangle_not_mem ht (originalPeriodPath_mem_rectangle ht hs)
  have sig {s : ℝ} (hs : s ∈ Icc (-1:ℝ) 1) : thetaSigmaKernel t a (z s) = A (z s) :=
    thetaSigmaKernel_eq_thetaA_of_pos ht ht _ pole (regular hs)
  have R {s : ℝ} (hs : s ∈ Icc (-1:ℝ) 1) : ellipticKernelRa t ht a (z s)*thetaSigmaKernel t a (z s) =
      -thetaAa t a (z s) := by
    have hm := mt (thetaJet_zero_iff_rhombic_lattice_of_pos ht (z s-a)).mpr
      (originalPath_shift_regular ht ha hs)
    have hl := thetaLa_eq_neg_ellipticKernelRa ht pole (regular hs) hm
      (originalPath_add_abscissa_not_mem ht ha hs)
    rw [sig hs,thetaAa,hl]
    dsimp only [A]
    ring
  have left : slopingIntegral t (fun w => ellipticKernelRa t ht a w*thetaSigmaKernel t a w) =
      -slopingIntegral t (thetaAa t a) := by
    unfold slopingIntegral
    rw [← mul_neg,← intervalIntegral.integral_neg]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    exact R (by simpa only [uIcc_of_le (by norm_num : (-1:ℝ)≤1)] using hs)
  have cz : Continuous z := continuous_iff_continuousAt.mpr fun s => (originalPeriodPath_hasDerivAt t s).continuousAt
  have cA : ContinuousOn (fun s => A (z s)) (Icc (-1:ℝ) 1) :=
    fun s hs => ((thetaA_analyticAt_off_lattice ht a (regular hs)).continuousAt.comp cz.continuousAt).continuousWithinAt
  have cP : ContinuousOn (fun s => L.weierstrassP (z s)) (Icc (-1:ℝ) 1) :=
    fun s hs => ((L.analyticOnNhd_weierstrassP _ (regular hs)).continuousAt.comp cz.continuousAt).continuousWithinAt
  have iPA := (cP.mul cA).intervalIntegrable_of_Icc (by norm_num : (-1:ℝ)≤1) (μ:=volume)
  have iA := cA.intervalIntegrable_of_Icc (by norm_num : (-1:ℝ)≤1) (μ:=volume)
  have right : slopingIntegral t (fun w => (L.weierstrassP w+eta)*thetaSigmaKernel t a w) =
      originalComplexWeight t ht a+eta*originalSlopingPeriod t a := by
    have eq : (∫ s : ℝ in (-1)..1, (L.weierstrassP (z s)+eta)*thetaSigmaKernel t a (z s)) =
        ∫ s : ℝ in (-1)..1, L.weierstrassP (z s)*A (z s)+eta*A (z s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      dsimp only
      rw [sig (s := s) (by simpa only [uIcc_of_le (by norm_num : (-1:ℝ)≤1)] using hs)]
      ring
    change q*_ = q*_+eta*(q*_)
    rw [eq]
    have split := intervalIntegral.integral_add iPA (iA.const_mul eta)
    simp only [Pi.mul_apply] at split
    rw [split,intervalIntegral.integral_const_mul]
    ring
  have da := (originalSlopingPeriod_a_hasDerivAt_integral ht ha).unique
    (originalSlopingPeriod_a_hasDerivAt ht ha)
  change slopingIntegral t _ = 2*thetaW t a*originalSigmaPeriod t a+
    2*((a:ℂ)-1)*slopingIntegral t (fun w => (L.weierstrassP w+eta)*thetaSigmaKernel t a w)
  rw [left,right,originalSigmaPeriod_eq_theta ht ha2,da]
  dsimp only [eta,thetaW]
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.original_sloping_logarithmic_period
