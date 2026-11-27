import TwoAxisHelicoid.RootDyadicTail

namespace TwoAxisHelicoid

def rootDyadicConfig : BallConfig := ⟨96,16,8⟩

theorem root_dyadic_tail_zero {t : ℝ} (ht : 86/100 ≤ t) (v : ℂ) (hv : |v.im| ≤ 1) :
    ‖thetaJet t 0 v-thetaPartial t 0 8 v‖ ≤
      (65536 : ℝ)/(DyadicBall.denominator rootDyadicConfig.prec : ℝ) := by
  exact rootDyadicTail0.remainder_bound rootDyadicConfig (86/100) 1 0 8 65536
    rootDyadicTail0_valid (by norm_num) (by simpa using ht) (by simpa using hv)

theorem root_dyadic_tail_one {t : ℝ} (ht : 86/100 ≤ t) (v : ℂ) (hv : |v.im| ≤ 1) :
    ‖thetaJet t 1 v-thetaPartial t 1 8 v‖ ≤
      (65536 : ℝ)/(DyadicBall.denominator rootDyadicConfig.prec : ℝ) := by
  exact rootDyadicTail1.remainder_bound rootDyadicConfig (86/100) 1 1 8 65536
    rootDyadicTail1_valid (by norm_num) (by simpa using ht) (by simpa using hv)

end TwoAxisHelicoid
