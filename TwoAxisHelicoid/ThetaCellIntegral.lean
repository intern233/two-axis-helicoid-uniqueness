import TwoAxisHelicoid.ThetaDisk
import TwoAxisHelicoid.BallQuadrature
import TwoAxisHelicoid.QuadratureError
import TwoAxisHelicoid.RationalQuadrature32

namespace TwoAxisHelicoid
open ComplexBall Metric

def quadratureErrorBound {K : ℕ} (q : QuadratureRule K) (N : ℕ) (h R M : ℚ) : ℚ :=
  (1+q.weightNorm)*(M*(h/R)^N/(1-h/R))

def evalThetaCellIntegral (cfg : BallConfig) (N : ℕ)
    (bt ba bc center : ComplexBall) (h R : ℚ) : Option ComplexBall :=
  if 0 ≤ h ∧ h < R then do
    let M ← evalThetaDisk cfg N bt ba bc center R
    let b ← evalThetaQuadrature cfg N rationalQuadrature32 bt ba bc center h
    pure (round cfg.prec (b.inflate (quadratureErrorBound rationalQuadrature32 32 h R M)))
  else none

/-- The returned disk contains the actual normalized cell integral, including
both finite arithmetic errors and the analytically proved quadrature remainder. -/
theorem evalThetaCellIntegral_sound {bt ba bc center : ComplexBall} {t a : ℝ} {c : ℂ}
    (ht : bt.Contains (t : ℂ)) (ha : ba.Contains (a : ℂ))
    (hc : bc.Contains (thetaACoefficient t a)) (hcenter : center.Contains c)
    (htpos : 0 < t) (cfg : BallConfig) (N : ℕ) (h R : ℚ) :
    Sound (evalThetaCellIntegral cfg N bt ba bc center h R)
      (normalizedIntegral (thetaA t a) c (h : ℝ)) := by
  unfold evalThetaCellIntegral
  split_ifs with hg
  · have hh : (0 : ℝ) ≤ h := by exact_mod_cast hg.1
    have hhR : (h : ℝ) < R := by exact_mod_cast hg.2
    cases hm : evalThetaDisk cfg N bt ba bc center R with
    | none => simp [Sound]
    | some M =>
      have hbound := evalThetaDisk_sound ht ha hc hcenter cfg N R hm
      have hM0 : (0 : ℝ) ≤ M := (norm_nonneg _).trans
        (hbound c (mem_closedBall_self (hh.trans hhR.le))).2
      have han := evalThetaDisk_holomorphic ht ha hc hcenter htpos cfg N R hm
      have herr := QuadratureRule.analytic_error_bound rationalQuadrature32_exact
        rationalQuadrature32_nodes hh hhR hM0 han
        (fun z hz => (hbound z (sphere_subset_closedBall hz)).2)
      have herr' : ‖normalizedIntegral (thetaA t a) c (h : ℝ)-
          rationalQuadrature32.apply (thetaA t a) c (h : ℝ)‖ ≤
          (quadratureErrorBound rationalQuadrature32 32 h R M : ℝ) := by
        simpa only [quadratureErrorBound, Rat.cast_mul, Rat.cast_add, Rat.cast_one,
          Rat.cast_div, Rat.cast_pow, Rat.cast_sub] using herr
      apply bind_sound (evalThetaQuadrature_sound ht ha hc hcenter cfg N rationalQuadrature32 h)
      intro b hb
      exact sound_some (round_contains (inflate_contains hb herr') cfg.prec)
  · simp [Sound]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.evalThetaCellIntegral_sound
