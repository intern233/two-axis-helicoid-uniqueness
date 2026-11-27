import TwoAxisHelicoid.PreciseExpressionPi
import TwoAxisHelicoid.DyadicCoefficientTrace
import TwoAxisHelicoid.FineRootPiDisk
import TwoAxisHelicoid.RootDyadicParameters

namespace TwoAxisHelicoid
def horizontalFineConfig : BallConfig := ⟨128,24,8⟩
def horizontalFinePi : DyadicBall := ⟨1069028584064966747859680373161870783301,0,2⟩
theorem horizontalFinePi_contains : (horizontalFinePi.toBall horizontalFineConfig.prec).Contains (Real.pi:ℂ) :=
  ComplexBall.coarsen_contains fineRootPiBall_contains (by decide +kernel)

namespace DyadicCoefficientTrace
def FineValid (cfg : BallConfig) (bp : DyadicBall) (N err : ℕ) (bq ba : DyadicBall)
    (w : DyadicCoefficientTrace) : Prop :=
  w.argument.WithPi cfg bp (threeDyadic ba .zero .zero) thetaArgumentExpression ∧
  w.argument.output.ChecksImOne cfg.prec ∧
  w.seedZero.Valid cfg .zero ∧ w.seedA.Valid cfg w.argument.output ∧
  w.thetaZero.Valid cfg 1 N err bq w.seedZero ∧ w.thetaA.Valid cfg 0 N err bq w.seedA ∧
  w.result.WithPi cfg bp (threeDyadic w.thetaZero.output w.thetaA.output .zero)
    thetaCoefficientExpression

instance (cfg : BallConfig) (bp : DyadicBall) (N err : ℕ) (bq ba : DyadicBall) (w : DyadicCoefficientTrace) :
    Decidable (w.FineValid cfg bp N err bq ba) := by unfold FineValid; infer_instance

theorem fine_sound {bq ba : DyadicBall} {t a : ℝ} (cfg : BallConfig) {bp : DyadicBall} (piOk : (bp.toBall cfg.prec).Contains (Real.pi:ℂ)) (N err : ℕ)
    (hq : (bq.toBall cfg.prec).Contains (Complex.exp (-Real.pi*t)))
    (ha : (ba.toBall cfg.prec).Contains (a : ℂ))
    (htail0 : ∀ v : ℂ, |v.im| ≤ 1 → ‖thetaJet t 0 v-thetaPartial t 0 N v‖ ≤
      (err : ℝ)/(DyadicBall.denominator cfg.prec : ℝ))
    (htail1 : ∀ v : ℂ, |v.im| ≤ 1 → ‖thetaJet t 1 v-thetaPartial t 1 N v‖ ≤
      (err : ℝ)/(DyadicBall.denominator cfg.prec : ℝ))
    (w : DyadicCoefficientTrace) (hw : w.FineValid cfg bp N err bq ba) :
    (w.output.toBall cfg.prec).Contains (thetaACoefficient t a) := by
  rcases hw with ⟨harg, hy, hs0, hsa, ht0, hta, hresult⟩
  have hz := DyadicBall.zero_contains cfg.prec
  have hv := w.argument.withPi_sound cfg piOk _ _ (threeDyadic_contains ha hz hz) _ harg
  rw [value_thetaArgumentExpression] at hv
  have hsz := w.seedZero.sound cfg hz hs0
  have hsv := w.seedA.sound cfg hv hsa
  have h0 := w.thetaZero.sound cfg 1 N err hq w.seedZero hsz (htail1 0 (by norm_num)) ht0
  have h1 := w.thetaA.sound cfg 0 N err hq w.seedA hsv
    (htail0 _ (DyadicBall.im_le_one hv hy)) hta
  have hout := w.result.withPi_sound cfg piOk _ _ (threeDyadic_contains h0 h1 hz) _ hresult
  rw [value_thetaCoefficientExpression] at hout
  exact hout

end DyadicCoefficientTrace

namespace DyadicThetaATrace
def FineValid (cfg : BallConfig) (bp : DyadicBall) (N err : ℕ) (bq ba bc bz : DyadicBall)
    (w : DyadicThetaATrace) : Prop :=
  w.argument.WithPi cfg bp (threeDyadic bz ba .zero) thetaArgumentExpression ∧
  w.shiftedArgument.WithPi cfg bp (threeDyadic bz ba .zero) thetaShiftedArgumentExpression ∧
  w.argument.output.ChecksImOne cfg.prec ∧
  w.shiftedArgument.output.ChecksImOne cfg.prec ∧
  w.seed.Valid cfg w.argument.output ∧ w.shiftedSeed.Valid cfg w.shiftedArgument.output ∧
  w.theta0.Valid cfg 0 N err bq w.seed ∧ w.theta1.Valid cfg 1 N err bq w.seed ∧
  w.thetaShifted.Valid cfg 0 N err bq w.shiftedSeed ∧ 0 < w.theta0.output.lower ∧
  w.result.WithPi cfg bp (fiveDyadic ba bc w.thetaShifted.output w.theta0.output w.theta1.output)
    thetaAFromJetsExpression

instance (cfg : BallConfig) (bp : DyadicBall) (N err : ℕ) (bq ba bc bz : DyadicBall) (w : DyadicThetaATrace) :
    Decidable (w.FineValid cfg bp N err bq ba bc bz) := by unfold FineValid; infer_instance

theorem fine_sound {bq ba bc bz : DyadicBall} {t a : ℝ} {z : ℂ}
    (cfg : BallConfig) {bp : DyadicBall} (piOk : (bp.toBall cfg.prec).Contains (Real.pi:ℂ)) (N err : ℕ)
    (hq : (bq.toBall cfg.prec).Contains (Complex.exp (-Real.pi*t)))
    (ha : (ba.toBall cfg.prec).Contains (a : ℂ))
    (hc : (bc.toBall cfg.prec).Contains (thetaACoefficient t a))
    (hz : (bz.toBall cfg.prec).Contains z)
    (htail0 : ∀ v : ℂ, |v.im| ≤ 1 → ‖thetaJet t 0 v-thetaPartial t 0 N v‖ ≤
      (err : ℝ)/(DyadicBall.denominator cfg.prec : ℝ))
    (htail1 : ∀ v : ℂ, |v.im| ≤ 1 → ‖thetaJet t 1 v-thetaPartial t 1 N v‖ ≤
      (err : ℝ)/(DyadicBall.denominator cfg.prec : ℝ))
    (w : DyadicThetaATrace) (hw : w.FineValid cfg bp N err bq ba bc bz) :
    (w.output.toBall cfg.prec).Contains (thetaA t a z) ∧ z ∈ thetaRegular t := by
  rcases hw with ⟨hav, ham, hyv, hym, hsv, hsm, ht0, ht1, htm, hlower, hresult⟩
  have he := threeDyadic_contains hz ha (DyadicBall.zero_contains cfg.prec)
  have hv := w.argument.withPi_sound cfg piOk _ _ he _ hav
  have hm := w.shiftedArgument.withPi_sound cfg piOk _ _ he _ ham
  rw [value_thetaArgumentExpression] at hv
  rw [value_thetaShiftedArgumentExpression] at hm
  have hvs := w.seed.sound cfg hv hsv
  have hms := w.shiftedSeed.sound cfg hm hsm
  have h0 := w.theta0.sound cfg 0 N err hq w.seed hvs
    (htail0 _ (DyadicBall.im_le_one hv hyv)) ht0
  have h1 := w.theta1.sound cfg 1 N err hq w.seed hvs
    (htail1 _ (DyadicBall.im_le_one hv hyv)) ht1
  have hshift := w.thetaShifted.sound cfg 0 N err hq w.shiftedSeed hms
    (htail0 _ (DyadicBall.im_le_one hm hym)) htm
  have hout := w.result.withPi_sound cfg piOk _ _ (fiveDyadic_contains ha hc hshift h0 h1) _ hresult
  rw [value_thetaAFromJetsExpression] at hout
  exact ⟨hout, ComplexBall.ne_zero_of_lower_pos h0 (DyadicBall.lower_pos_toBall hlower)⟩

end DyadicThetaATrace

def RootDyadicParameters.HorizontalFineValid (w : RootDyadicParameters) (tlo thi alo ahi : ℚ) : Prop :=
  86/100≤tlo ∧
  (w.height.toBall 128).coarsens (ComplexBall.realInterval tlo thi) ∧
  (w.abscissa.toBall 128).coarsens (ComplexBall.realInterval alo ahi) ∧
  w.q.WithPi horizontalFineConfig horizontalFinePi (threeDyadic w.height .zero .zero) thetaQExpression ∧
  w.coefficient.FineValid horizontalFineConfig horizontalFinePi 8 (2^48) w.q.output w.abscissa

instance (w : RootDyadicParameters) (l u a b : ℚ) : Decidable (w.HorizontalFineValid l u a b) := by
  unfold RootDyadicParameters.HorizontalFineValid
  infer_instance

theorem horizontalFine_tail {t : ℝ} (ht : 86/100≤t) (j : ℕ) (hj : j≤1) (v : ℂ) (hv : |v.im|≤1) :
    ‖thetaJet t j v-thetaPartial t j 8 v‖≤((2^48:ℕ):ℝ)/(DyadicBall.denominator horizontalFineConfig.prec:ℝ) := by
  have conv : (65536:ℝ)/(DyadicBall.denominator rootDyadicConfig.prec:ℝ)=
      ((2^48:ℕ):ℝ)/(DyadicBall.denominator horizontalFineConfig.prec:ℝ) := by
    norm_num [rootDyadicConfig,horizontalFineConfig,DyadicBall.denominator]
  rw [← conv]
  interval_cases j
  · exact root_dyadic_tail_zero ht v hv
  · exact root_dyadic_tail_one ht v hv

theorem RootDyadicParameters.horizontalFine_sound (w : RootDyadicParameters)
    {l u al au : ℚ} (ok : w.HorizontalFineValid l u al au) {t a : ℝ}
    (hl : (l:ℝ)≤t) (hu : t≤(u:ℝ)) (hal : (al:ℝ)≤a) (hau : a≤(au:ℝ)) :
    86/100≤t ∧ (w.q.output.toBall 128).Contains (Complex.exp (-Real.pi*t)) ∧
    (w.abscissa.toBall 128).Contains (a:ℂ) ∧ (w.coefficient.output.toBall 128).Contains (thetaACoefficient t a) := by
  obtain ⟨lower,h,aBall,q,cf⟩ := ok
  have lc : ((86/100:ℚ):ℝ)≤(l:ℝ) := Rat.cast_le.mpr lower
  have ht : 86/100≤t := by simpa only [Rat.cast_div,Rat.cast_ofNat] using lc.trans hl
  have hz := DyadicBall.zero_contains horizontalFineConfig.prec
  have bt := ComplexBall.coarsen_contains (ComplexBall.realInterval_contains hl hu) h
  have ba := ComplexBall.coarsen_contains (ComplexBall.realInterval_contains hal hau) aBall
  have bq := w.q.withPi_sound horizontalFineConfig horizontalFinePi_contains _ _ (threeDyadic_contains bt hz hz) _ q
  have bn : (w.q.output.toBall 128).Contains (Complex.exp (-Real.pi*t)) := by
    simpa only [horizontalFineConfig,thetaQExpression,BallExpression.value,threeValues,neg_mul] using bq
  exact ⟨ht,bn,ba,w.coefficient.fine_sound horizontalFineConfig horizontalFinePi_contains 8 (2^48)
    bn ba (horizontalFine_tail ht 0 (by norm_num)) (horizontalFine_tail ht 1 le_rfl) cf⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.DyadicThetaATrace.fine_sound
#print axioms TwoAxisHelicoid.RootDyadicParameters.horizontalFine_sound
