import TwoAxisHelicoid.DyadicThetaSeed

namespace TwoAxisHelicoid
open ComplexBall BallExpression

structure DyadicThetaTail where
  majorant : DyadicExpressionTrace
  ratio : DyadicExpressionTrace
  deriving Repr

namespace DyadicThetaTail

def Valid (cfg : BallConfig) (tlo y : ℚ) (j N err : ℕ) (w : DyadicThetaTail) : Prop :=
  w.majorant.Valid cfg (fun _ => .zero) (thetaMajorantExpression tlo y j N) ∧
  w.ratio.Valid cfg (fun _ => .zero) (thetaRatioExpression tlo y j N) ∧
  let B := w.majorant.output.toBall cfg.prec
  let R := w.ratio.output.toBall cfg.prec
  R.center.re+R.radius < 1 ∧
    (B.center.re+B.radius)/(1-(R.center.re+R.radius)) ≤
      (err : ℚ)/(DyadicBall.denominator cfg.prec : ℚ)

instance (cfg : BallConfig) (tlo y : ℚ) (j N err : ℕ) (w : DyadicThetaTail) :
    Decidable (w.Valid cfg tlo y j N err) := by unfold Valid; infer_instance

theorem sound (cfg : BallConfig) (tlo y : ℚ) (j N err : ℕ) (w : DyadicThetaTail)
    (hw : w.Valid cfg tlo y j N err) :
    thetaRatio tlo y j N < 1 ∧
      thetaMajorant tlo y j N/(1-thetaRatio tlo y j N) ≤
        (err : ℝ)/(DyadicBall.denominator cfg.prec : ℝ) := by
  have hb := w.majorant.sound cfg _ (fun _ => 0)
    (fun _ => DyadicBall.zero_contains cfg.prec) _ hw.1
  have hr := w.ratio.sound cfg _ (fun _ => 0)
    (fun _ => DyadicBall.zero_contains cfg.prec) _ hw.2.1
  rw [value_thetaMajorantExpression] at hb
  rw [value_thetaRatioExpression] at hr
  have hbb := (re_bounds hb).2
  have hrr := (re_bounds hr).2
  simp only [Complex.ofReal_re] at hbb hrr
  have hgu : (((w.ratio.output.toBall cfg.prec).center.re+
      (w.ratio.output.toBall cfg.prec).radius : ℚ) : ℝ) < 1 := by
    exact_mod_cast hw.2.2.1
  have hrho : thetaRatio tlo y j N < 1 := hrr.trans_lt hgu
  refine ⟨hrho, ?_⟩
  have hc : (((w.majorant.output.toBall cfg.prec).center.re+
        (w.majorant.output.toBall cfg.prec).radius : ℚ) : ℝ)/
      (1-(((w.ratio.output.toBall cfg.prec).center.re+
        (w.ratio.output.toBall cfg.prec).radius : ℚ) : ℝ)) ≤
      (err : ℝ)/(DyadicBall.denominator cfg.prec : ℝ) := by
    exact_mod_cast hw.2.2.2
  apply le_trans _ hc
  calc
    _ ≤ (((w.majorant.output.toBall cfg.prec).center.re+
        (w.majorant.output.toBall cfg.prec).radius : ℚ) : ℝ)/
        (1-thetaRatio tlo y j N) := div_le_div_of_nonneg_right hbb (by linarith)
    _ ≤ _ := div_le_div_of_nonneg_left
      ((thetaMajorant_nonneg _ _ _ _).trans hbb) (by linarith) (by linarith)

theorem remainder_bound {t : ℝ} {v : ℂ} (cfg : BallConfig) (tlo y : ℚ)
    (j N err : ℕ) (w : DyadicThetaTail) (hw : w.Valid cfg tlo y j N err)
    (htlo : (0 : ℝ) < tlo) (ht : (tlo : ℝ) ≤ t) (hv : |v.im| ≤ (y : ℝ)) :
    ‖thetaJet t j v-thetaPartial t j N v‖ ≤
      (err : ℝ)/(DyadicBall.denominator cfg.prec : ℝ) := by
  have h := w.sound cfg tlo y j N err hw
  exact (thetaJet_tail_bound htlo ht hv j N h.1).trans h.2

end DyadicThetaTail
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.DyadicThetaTail.remainder_bound
