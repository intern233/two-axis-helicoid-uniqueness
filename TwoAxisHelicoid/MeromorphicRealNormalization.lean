import TwoAxisHelicoid.CommonPrincipalPartRigidity
import TwoAxisHelicoid.MeromorphicChartPoles

namespace TwoAxisHelicoid
open Complex Set Filter Metric
open scoped Topology

/-- Intrinsic poles expressed in coordinate coefficients: a point is a pole
if every chart containing it has a nonanalytic coefficient there. -/
def chartPoleSet {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (F : X → ℂ → ℂ) : Set X :=
  {x | ∀ p : X, x ∈ (chartAt ℂ p).source → ¬ AnalyticAt ℂ (F p) (chartAt ℂ p x)}

/-- Coordinate presentation of two meromorphic one-forms with identical
principal parts. This contains local Laurent data and meromorphy, but no
global primitive, no finite-pole assumption and no equality conclusion.
The theorem is valid without using additional overlap compatibility; in
particular it applies to compatible coefficients of genuine one-forms. -/
structure MeromorphicPairInCharts (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] where
  left : X → ℂ → ℂ
  right : X → ℂ → ℂ
  meromorphicLeft : ∀ p : X, MeromorphicAt (left p) (chartAt ℂ p p)
  meromorphicRight : ∀ p : X, MeromorphicAt (right p) (chartAt ℂ p p)
  regularLeft : HolomorphicCoefficientDisks X
  regularRight : X → ℂ → ℂ
  analyticRight : ∀ p z, z ∈ ball (chartAt ℂ p p) (regularLeft.radius p) →
    AnalyticAt ℂ (regularRight p) z
  order : X → ℕ
  order_zero_off : ∀ p, p ∉ chartPoleSet left → order p = 0
  principalCoefficient : X → ℕ → ℂ
  left_eq : ∀ p z, z ∈ ball (chartAt ℂ p p) (regularLeft.radius p) →
    (chartAt ℂ p).symm z ∉ chartPoleSet left →
    left p z = finitePrincipalPart (order p) (principalCoefficient p) (chartAt ℂ p p) z+
      regularLeft.coefficient p z
  right_eq : ∀ p z, z ∈ ball (chartAt ℂ p p) (regularLeft.radius p) →
    (chartAt ℂ p).symm z ∉ chartPoleSet left →
    right p z = finitePrincipalPart (order p) (principalCoefficient p) (chartAt ℂ p p) z+
      regularRight p z

namespace MeromorphicPairInCharts
variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

theorem poles_finite [CompactSpace X] (D : MeromorphicPairInCharts X) :
    (chartPoleSet D.left).Finite :=
  meromorphic_chart_poles_finite D.meromorphicLeft (fun p _x hx hP => hP p hx)

noncomputable def common [CompactSpace X] (D : MeromorphicPairInCharts X) :
    CommonPrincipalPartDisks X where
  poles := chartPoleSet D.left
  poles_finite := D.poles_finite
  radius := D.regularLeft.radius
  radius_pos := D.regularLeft.radius_pos
  ball_target := D.regularLeft.ball_target
  order := D.order
  order_zero_off := D.order_zero_off
  principalCoefficient := D.principalCoefficient
  left := D.left
  right := D.right
  regularLeft := D.regularLeft.coefficient
  regularRight := D.regularRight
  analyticLeft := D.regularLeft.analytic
  analyticRight := D.analyticRight
  left_eq := D.left_eq
  right_eq := D.right_eq

/-- Appendix C.1 in local-coordinate form. Compactness supplies finiteness of
poles; cancellation supplies a holomorphic differential; the actual zero real
periods supply a global harmonic primitive. Equality includes punctured germs
at poles, rather than arbitrary assigned values at the singular points. -/
theorem real_normalized_meromorphic_germs_equal [CompactSpace X] [PreconnectedSpace X]
    (D : MeromorphicPairInCharts X)
    (hL : D.common.difference.ZeroRealAvoidingPeriods (chartPoleSet D.left)ᶜ D.left)
    (hR : D.common.difference.ZeroRealAvoidingPeriods (chartPoleSet D.left)ᶜ D.right) (p : X) :
    D.left p =ᶠ[𝓝[≠] (chartAt ℂ p p)] D.right p :=
  D.common.germs_equal hL hR p

theorem real_normalized_meromorphic_coefficients_equal [CompactSpace X] [PreconnectedSpace X]
    (D : MeromorphicPairInCharts X)
    (hL : D.common.difference.ZeroRealAvoidingPeriods (chartPoleSet D.left)ᶜ D.left)
    (hR : D.common.difference.ZeroRealAvoidingPeriods (chartPoleSet D.left)ᶜ D.right)
    (p : X) {z : ℂ} (hz : z ∈ ball (chartAt ℂ p p) (D.regularLeft.radius p))
    (hreg : (chartAt ℂ p).symm z ∉ chartPoleSet D.left) : D.left p z = D.right p z :=
  D.common.coefficients_equal hL hR p hz hreg

end MeromorphicPairInCharts
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.MeromorphicPairInCharts.real_normalized_meromorphic_germs_equal
#print axioms TwoAxisHelicoid.MeromorphicPairInCharts.real_normalized_meromorphic_coefficients_equal
