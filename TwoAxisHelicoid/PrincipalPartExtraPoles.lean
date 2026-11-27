import TwoAxisHelicoid.MeromorphicRealNormalization

namespace TwoAxisHelicoid
open Complex Set Metric

namespace CommonPrincipalPartDisks
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

/-- One may remove additional finitely many ordinary points from all period
paths, for example the zeros of a Gauss map when comparing height forms. -/
noncomputable def withExtraPoles (D : CommonPrincipalPartDisks M)
    (P : Set M) (hP : P.Finite) (hsub : D.poles ⊆ P) : CommonPrincipalPartDisks M :=
  { D with
    poles := P
    poles_finite := hP
    order_zero_off := fun p hp => D.order_zero_off p (fun h => hp (hsub h))
    left_eq := fun p z hz hr => D.left_eq p z hz (fun h => hr (hsub h))
    right_eq := fun p z hz hr => D.right_eq p z hz (fun h => hr (hsub h)) }

theorem coefficients_equal_avoiding_extra_poles [CompactSpace M] [PreconnectedSpace M]
    (D : CommonPrincipalPartDisks M) {P : Set M} (hP : P.Finite) (hsub : D.poles ⊆ P)
    (hL : D.difference.ZeroRealAvoidingPeriods Pᶜ D.left)
    (hR : D.difference.ZeroRealAvoidingPeriods Pᶜ D.right)
    (p : M) {z : ℂ} (hz : z ∈ ball (chartAt ℂ p p) (D.radius p))
    (hr : (chartAt ℂ p).symm z ∉ P) : D.left p z = D.right p z :=
  (D.withExtraPoles P hP hsub).coefficients_equal hL hR p hz hr

end CommonPrincipalPartDisks

namespace HolomorphicCoefficientDisks
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

/-- Coordinate disks small enough for two local differential presentations.
The zero coefficient only selects the disks and makes no claim about either
of the actual forms under consideration. -/
noncomputable def commonDisks (A B : HolomorphicCoefficientDisks M) :
    HolomorphicCoefficientDisks M where
  radius p := min (A.radius p) (B.radius p)
  radius_pos p := lt_min (A.radius_pos p) (B.radius_pos p)
  ball_target p _z hz := A.ball_target p ((ball_subset_ball (min_le_left _ _)) hz)
  coefficient _ _ := 0
  analytic _ _ _ := analyticAt_const

theorem commonDisks_mem_left (A B : HolomorphicCoefficientDisks M) (p : M) {z : ℂ}
    (hz : z ∈ ball (chartAt ℂ p p) ((A.commonDisks B).radius p)) :
    z ∈ ball (chartAt ℂ p p) (A.radius p) :=
  ball_subset_ball (min_le_left _ _) hz

theorem commonDisks_mem_right (A B : HolomorphicCoefficientDisks M) (p : M) {z : ℂ}
    (hz : z ∈ ball (chartAt ℂ p p) ((A.commonDisks B).radius p)) :
    z ∈ ball (chartAt ℂ p p) (B.radius p) :=
  ball_subset_ball (min_le_right _ _) hz

end HolomorphicCoefficientDisks
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.CommonPrincipalPartDisks.coefficients_equal_avoiding_extra_poles
