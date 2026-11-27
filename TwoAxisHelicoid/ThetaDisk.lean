import TwoAxisHelicoid.HorizontalEnclosure

namespace TwoAxisHelicoid
open ComplexBall Metric

def ComplexBall.inflate (b : ComplexBall) (r : ℚ) : ComplexBall := ⟨b.center, b.radius+r⟩

theorem ComplexBall.inflate_contains {b : ComplexBall} {c z : ℂ} {r : ℚ}
    (hc : b.Contains c) (hz : ‖z-c‖ ≤ (r : ℝ)) : (b.inflate r).Contains z := by
  unfold Contains inflate at *
  dsimp
  push_cast
  have hn := norm_add_le (z-c) (c-b.center.val)
  rw [sub_add_sub_cancel] at hn
  linarith

def evalThetaDisk (cfg : BallConfig) (N : ℕ)
    (bt ba bc center : ComplexBall) (R : ℚ) : Option ℚ := do
  let disk := center.inflate R
  let sz ← evalThetaFast cfg 0 N bt (complexArgumentBall cfg disk)
  if 0 < sz.lower then do
    let out ← evalThetaAWithCoefficient cfg N bt ba bc disk
    pure (out.center.absUpper+out.radius)
  else none

theorem evalThetaDisk_sound {bt ba bc center : ComplexBall} {t a : ℝ} {c : ℂ}
    (ht : bt.Contains (t : ℂ)) (ha : ba.Contains (a : ℂ))
    (hc : bc.Contains (thetaACoefficient t a)) (hcenter : center.Contains c)
    (cfg : BallConfig) (N : ℕ) (R : ℚ) {M : ℚ}
    (he : evalThetaDisk cfg N bt ba bc center R = some M) :
    ∀ z ∈ closedBall c (R : ℝ), z ∈ thetaRegular t ∧ ‖thetaA t a z‖ ≤ (M : ℝ) := by
  intro z hz
  have hdisk := inflate_contains hcenter (mem_closedBall_iff_norm.mp hz)
  have hs := evalThetaFast_sound ht (complexArgumentBall_contains hdisk cfg) cfg 0 N
  have hv := evalThetaAWithCoefficient_sound ht ha hc hdisk cfg N
  unfold evalThetaDisk at he
  cases hsout : evalThetaFast cfg 0 N bt (complexArgumentBall cfg (center.inflate R)) with
  | none => simp [hsout] at he
  | some sz =>
    simp only [hsout] at he
    change (if 0 < sz.lower then
      (evalThetaAWithCoefficient cfg N bt ba bc (center.inflate R)).bind
        (fun out => some (out.center.absUpper+out.radius)) else none) = some M at he
    split_ifs at he with hg
    · cases hout : evalThetaAWithCoefficient cfg N bt ba bc (center.inflate R) with
      | none => simp [hout] at he
      | some out =>
        simp only [hout] at he
        change some (out.center.absUpper+out.radius) = some M at he
        have he := Option.some.inj he
        subst M
        exact ⟨ne_zero_of_lower_pos (hs sz hsout) hg, norm_le (hv out hout)⟩

theorem evalThetaDisk_holomorphic {bt ba bc center : ComplexBall} {t a : ℝ} {c : ℂ}
    (ht : bt.Contains (t : ℂ)) (ha : ba.Contains (a : ℂ))
    (hc : bc.Contains (thetaACoefficient t a)) (hcenter : center.Contains c)
    (htpos : 0 < t) (cfg : BallConfig) (N : ℕ) (R : ℚ) {M : ℚ}
    (he : evalThetaDisk cfg N bt ba bc center R = some M) :
    DiffContOnCl ℂ (thetaA t a) (ball c (R : ℝ)) := by
  apply (thetaA_differentiableOn htpos a).diffContOnCl_ball
  intro z hz
  exact (evalThetaDisk_sound ht ha hc hcenter cfg N R he z hz).1

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.evalThetaDisk_holomorphic
