import TwoAxisHelicoid.DyadicThetaTailFast

namespace TwoAxisHelicoid

/-- Uniform tail data for horizontal periods, including a configurable imaginary strip. -/
structure HorizontalRangeSetup where
  config : BallConfig
  lower : ℚ
  imaginary : ℚ
  terms : ℕ
  error : ℕ
  tails : Fin 2 → DyadicThetaTail

namespace HorizontalRangeSetup

def Valid (s : HorizontalRangeSetup) : Prop :=
  0 < s.lower ∧ 1 ≤ s.imaginary ∧ ∀ j : Fin 2,
    (s.tails j).Checks s.config s.lower s.imaginary j s.terms s.error

instance (s : HorizontalRangeSetup) : Decidable s.Valid := by
  unfold Valid
  infer_instance

theorem lower_pos (s : HorizontalRangeSetup) (hs : s.Valid) : (0 : ℝ) < s.lower := by
  exact_mod_cast hs.1

theorem tail_bound (s : HorizontalRangeSetup) (hs : s.Valid) {t : ℝ}
    (ht : (s.lower : ℝ) ≤ t) (j : Fin 2) (v : ℂ) (hv : |v.im| ≤ s.imaginary) :
    ‖thetaJet t j v - thetaPartial t j s.terms v‖ ≤
      (s.error : ℝ) / (DyadicBall.denominator s.config.prec : ℝ) := by
  exact (s.tails j).remainder_bound s.config s.lower s.imaginary j s.terms s.error
    (DyadicThetaTail.valid_of_checks (hs.2.2 j)) (s.lower_pos hs) ht hv

theorem tail_bound_one (s : HorizontalRangeSetup) (hs : s.Valid) {t : ℝ}
    (ht : (s.lower : ℝ) ≤ t) (j : Fin 2) (v : ℂ) (hv : |v.im| ≤ 1) :
    ‖thetaJet t j v - thetaPartial t j s.terms v‖ ≤
      (s.error : ℝ) / (DyadicBall.denominator s.config.prec : ℝ) := by
  apply s.tail_bound hs ht j v
  exact hv.trans (by exact_mod_cast hs.2.1)

end HorizontalRangeSetup
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.HorizontalRangeSetup.tail_bound
