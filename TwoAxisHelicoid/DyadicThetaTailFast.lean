import TwoAxisHelicoid.DyadicThetaTail

namespace TwoAxisHelicoid.DyadicThetaTail

def Checks (cfg : BallConfig) (tlo y : ℚ) (j N err : ℕ) (w : DyadicThetaTail) : Prop :=
  w.majorant.Valid cfg (fun _ => .zero) (BallExpression.thetaMajorantExpression tlo y j N) ∧
  w.ratio.Valid cfg (fun _ => .zero) (BallExpression.thetaRatioExpression tlo y j N) ∧
  w.ratio.output.re+(w.ratio.output.radius : ℤ) < DyadicBall.denominator cfg.prec ∧
  (w.majorant.output.re+(w.majorant.output.radius : ℤ))*DyadicBall.denominator cfg.prec ≤
    (err : ℤ)*(DyadicBall.denominator cfg.prec-(w.ratio.output.re+(w.ratio.output.radius : ℤ)))

instance (cfg : BallConfig) (tlo y : ℚ) (j N err : ℕ) (w : DyadicThetaTail) :
    Decidable (w.Checks cfg tlo y j N err) := by unfold Checks; infer_instance

theorem valid_of_checks {cfg : BallConfig} {tlo y : ℚ} {j N err : ℕ} {w : DyadicThetaTail}
    (hw : w.Checks cfg tlo y j N err) : w.Valid cfg tlo y j N err := by
  refine ⟨hw.1, hw.2.1, ?_, ?_⟩
  · have hd : (0 : ℚ) < DyadicBall.denominator cfg.prec := by
      exact_mod_cast DyadicBall.denominator_pos cfg.prec
    have hr : (w.ratio.output.re : ℚ)+(w.ratio.output.radius : ℚ) <
        (DyadicBall.denominator cfg.prec : ℚ) := by exact_mod_cast hw.2.2.1
    change (w.ratio.output.re : ℚ)/DyadicBall.denominator cfg.prec+
      (w.ratio.output.radius : ℚ)/DyadicBall.denominator cfg.prec < 1
    rw [← add_div]
    exact (div_lt_one hd).mpr hr
  · let D : ℚ := DyadicBall.denominator cfg.prec
    let B : ℚ := (w.majorant.output.re : ℚ)+w.majorant.output.radius
    let R : ℚ := (w.ratio.output.re : ℚ)+w.ratio.output.radius
    have hd : 0 < D := by dsimp [D]; exact_mod_cast DyadicBall.denominator_pos cfg.prec
    have hr : R < D := by dsimp [R,D]; exact_mod_cast hw.2.2.1
    have he : B*D ≤ (err : ℚ)*(D-R) := by dsimp [B,D,R]; exact_mod_cast hw.2.2.2
    have hr' : 0 < D-R := sub_pos.mpr hr
    change (((w.majorant.output.re : ℚ)/D+(w.majorant.output.radius : ℚ)/D)/
      (1-((w.ratio.output.re : ℚ)/D+(w.ratio.output.radius : ℚ)/D))) ≤ (err : ℚ)/D
    rw [← add_div, ← add_div]
    change (B/D)/(1-R/D) ≤ (err : ℚ)/D
    have hquot : (B/D)/(1-R/D) = B/(D-R) := by field_simp
    rw [hquot]
    exact (div_le_div_iff₀ hr' hd).mpr he

end TwoAxisHelicoid.DyadicThetaTail
