import TwoAxisHelicoid.DyadicThetaTailFast

namespace TwoAxisHelicoid

/-- A checked numerical configuration, with uniform tails for the first five jets. -/
structure RangeCertificateSetup where
  config : BallConfig
  lower : ℚ
  terms : ℕ
  error : ℕ
  tails : Fin 5 → DyadicThetaTail

namespace RangeCertificateSetup

def Valid (s : RangeCertificateSetup) : Prop :=
  0 < s.lower ∧ ∀ j : Fin 5,
    (s.tails j).Checks s.config s.lower 1 j s.terms s.error

instance (s : RangeCertificateSetup) : Decidable s.Valid := by
  unfold Valid
  infer_instance

theorem lower_pos (s : RangeCertificateSetup) (hs : s.Valid) : (0 : ℝ) < s.lower := by
  exact_mod_cast hs.1

theorem tail_bound (s : RangeCertificateSetup) (hs : s.Valid) {t : ℝ}
    (ht : (s.lower : ℝ) ≤ t) (j : Fin 5) (v : ℂ) (hv : |v.im| ≤ 1) :
    ‖thetaJet t j v - thetaPartial t j s.terms v‖ ≤
      (s.error : ℝ) / (DyadicBall.denominator s.config.prec : ℝ) := by
  exact (s.tails j).remainder_bound s.config s.lower 1 j s.terms s.error
    (DyadicThetaTail.valid_of_checks (hs.2 j)) (s.lower_pos hs) ht (by simpa using hv)

end RangeCertificateSetup
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.RangeCertificateSetup.tail_bound
