import TwoAxisHelicoid.RealPeriodPrimitive
import Mathlib.Analysis.Complex.HasPrimitives

namespace TwoAxisHelicoid
open Complex Set Metric

/-- Holomorphic coefficients on coordinate disks. Compatibility on overlaps
may be imposed when this data represents a differential; the zero-period
theorem below in fact works without requiring that extra hypothesis. -/
structure HolomorphicCoefficientDisks (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] where
  radius : X → ℝ
  radius_pos : ∀ p, 0 < radius p
  ball_target : ∀ p, ball (chartAt ℂ p p) (radius p) ⊆ (chartAt ℂ p).target
  coefficient : X → ℂ → ℂ
  analytic : ∀ p z, z ∈ ball (chartAt ℂ p p) (radius p) → AnalyticAt ℂ (coefficient p) z

namespace HolomorphicCoefficientDisks
variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

noncomputable def localIntegral (A : HolomorphicCoefficientDisks X) (p : X) (z : ℂ) : ℂ :=
  wedgeIntegral (chartAt ℂ p p) z (A.coefficient p)

theorem localIntegral_hasDerivAt (A : HolomorphicCoefficientDisks X) (p : X) {z : ℂ}
    (hz : z ∈ ball (chartAt ℂ p p) (A.radius p)) :
    HasDerivAt (A.localIntegral p) (A.coefficient p z) z := by
  have hd : DifferentiableOn ℂ (A.coefficient p) (ball (chartAt ℂ p p) (A.radius p)) :=
    fun w hw => (A.analytic p w hw).differentiableAt.differentiableWithinAt
  exact hd.isConservativeOn.hasDerivAt_wedgeIntegral hd.continuousOn hz

theorem localIntegral_analyticAt (A : HolomorphicCoefficientDisks X) (p : X) {z : ℂ}
    (hz : z ∈ ball (chartAt ℂ p p) (A.radius p)) : AnalyticAt ℂ (A.localIntegral p) z :=
  DifferentiableOn.analyticAt
    (fun _ hw => (A.localIntegral_hasDerivAt p hw).differentiableAt.differentiableWithinAt)
    (isOpen_ball.mem_nhds hz)

noncomputable def primitives (A : HolomorphicCoefficientDisks X) : HolomorphicPrimitiveDisks X where
  radius := A.radius
  radius_pos := A.radius_pos
  ball_target := A.ball_target
  primitive := A.localIntegral
  analytic := fun p _ hz => A.localIntegral_analyticAt p hz

/-- This condition concerns actual interval integrals of the local
coefficients: sums of real increments around every finite closed chain of
coordinate disks vanish. It does not assume a global harmonic function. -/
def ZeroRealPeriods (A : HolomorphicCoefficientDisks X) : Prop :=
  A.primitives.ZeroRealPeriods

theorem zero_of_zero_real_periods [CompactSpace X] [PreconnectedSpace X]
    {A : HolomorphicCoefficientDisks X} (hP : A.ZeroRealPeriods) (p : X) :
    A.coefficient p (chartAt ℂ p p) = 0 := by
  have hz := A.primitives.coefficient_zero_of_zero_real_periods hP p
  change deriv (A.localIntegral p) (chartAt ℂ p p) = 0 at hz
  rwa [(A.localIntegral_hasDerivAt p (mem_ball_self (A.radius_pos p))).deriv] at hz

end HolomorphicCoefficientDisks
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.HolomorphicCoefficientDisks.zero_of_zero_real_periods
