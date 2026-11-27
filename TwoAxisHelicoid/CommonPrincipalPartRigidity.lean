import TwoAxisHelicoid.ChartFinitePoles

namespace TwoAxisHelicoid
open Complex Set Filter Metric
open scoped Topology
set_option maxHeartbeats 1000000

/-- The finite negative-power part of a Laurent expansion. -/
noncomputable def finitePrincipalPart (n : ℕ) (c : ℕ → ℂ) (a z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range n, c k/(z-a)^(k+1)

theorem finitePrincipalPart_analyticAt {n : ℕ} {c : ℕ → ℂ} {a z : ℂ}
    (hz : z ≠ a) : AnalyticAt ℂ (finitePrincipalPart n c a) z := by
  apply Finset.analyticAt_fun_sum
  intro k _
  exact analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow (k+1))
    (pow_ne_zero _ (sub_ne_zero.mpr hz))

/-- Two local presentations of meromorphic differentials with the same
finite Laurent principal part on each coordinate disk. Pole values themselves
are immaterial; the formulas are required on the regular locus. -/
structure CommonPrincipalPartDisks (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] where
  poles : Set X
  poles_finite : poles.Finite
  radius : X → ℝ
  radius_pos : ∀ p, 0 < radius p
  ball_target : ∀ p, ball (chartAt ℂ p p) (radius p) ⊆ (chartAt ℂ p).target
  order : X → ℕ
  order_zero_off : ∀ p, p ∉ poles → order p = 0
  principalCoefficient : X → ℕ → ℂ
  left : X → ℂ → ℂ
  right : X → ℂ → ℂ
  regularLeft : X → ℂ → ℂ
  regularRight : X → ℂ → ℂ
  analyticLeft : ∀ p z, z ∈ ball (chartAt ℂ p p) (radius p) → AnalyticAt ℂ (regularLeft p) z
  analyticRight : ∀ p z, z ∈ ball (chartAt ℂ p p) (radius p) → AnalyticAt ℂ (regularRight p) z
  left_eq : ∀ p z, z ∈ ball (chartAt ℂ p p) (radius p) → (chartAt ℂ p).symm z ∉ poles →
    left p z = finitePrincipalPart (order p) (principalCoefficient p) (chartAt ℂ p p) z+regularLeft p z
  right_eq : ∀ p z, z ∈ ball (chartAt ℂ p p) (radius p) → (chartAt ℂ p).symm z ∉ poles →
    right p z = finitePrincipalPart (order p) (principalCoefficient p) (chartAt ℂ p p) z+regularRight p z

namespace CommonPrincipalPartDisks
variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The holomorphic difference is constructed by cancelling the common
principal part. It is not assumed as a separate global primitive. -/
noncomputable def difference (D : CommonPrincipalPartDisks X) : HolomorphicCoefficientDisks X where
  radius := D.radius
  radius_pos := D.radius_pos
  ball_target := D.ball_target
  coefficient p z := D.regularLeft p z-D.regularRight p z
  analytic p z hz := (D.analyticLeft p z hz).sub (D.analyticRight p z hz)

theorem regular_neighborhood (D : CommonPrincipalPartDisks X) (p : X) {z : ℂ}
    (hz : z ∈ ball (chartAt ℂ p p) (D.radius p)) (hreg : (chartAt ℂ p).symm z ∉ D.poles) :
    ∀ᶠ w in 𝓝 z, w ∈ ball (chartAt ℂ p p) (D.radius p) ∧ (chartAt ℂ p).symm w ∉ D.poles := by
  have hnot := (D.difference.chart_regular_iff D.poles p hz).mp hreg
  have ho := (HolomorphicCoefficientDisks.chartPoles_finite D.poles_finite p).isClosed.isOpen_compl
  filter_upwards [isOpen_ball.mem_nhds hz,ho.mem_nhds hnot] with w hw hn
  exact ⟨hw,(D.difference.chart_regular_iff D.poles p hw).mpr hn⟩

theorem principalPart_analyticAt_regular (D : CommonPrincipalPartDisks X) (p : X) {z : ℂ}
    (hreg : (chartAt ℂ p).symm z ∉ D.poles) :
    AnalyticAt ℂ (finitePrincipalPart (D.order p) (D.principalCoefficient p) (chartAt ℂ p p)) z := by
  by_cases hp : p ∈ D.poles
  · apply finitePrincipalPart_analyticAt
    intro he
    rw [he,(chartAt ℂ p).left_inv (mem_chart_source ℂ p)] at hreg
    exact hreg hp
  · rw [D.order_zero_off p hp]
    simpa only [finitePrincipalPart,Finset.range_zero,Finset.sum_empty] using!
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) z)

theorem left_continuousAt_regular (D : CommonPrincipalPartDisks X) (p : X) {z : ℂ}
    (hz : z ∈ ball (chartAt ℂ p p) (D.radius p)) (hreg : (chartAt ℂ p).symm z ∉ D.poles) :
    ContinuousAt (D.left p) z := by
  apply ((D.principalPart_analyticAt_regular p hreg).add (D.analyticLeft p z hz)).continuousAt.congr_of_eventuallyEq
  filter_upwards [D.regular_neighborhood p hz hreg] with w hw
  exact D.left_eq p w hw.1 hw.2

theorem right_continuousAt_regular (D : CommonPrincipalPartDisks X) (p : X) {z : ℂ}
    (hz : z ∈ ball (chartAt ℂ p p) (D.radius p)) (hreg : (chartAt ℂ p).symm z ∉ D.poles) :
    ContinuousAt (D.right p) z := by
  apply ((D.principalPart_analyticAt_regular p hreg).add (D.analyticRight p z hz)).continuousAt.congr_of_eventuallyEq
  filter_upwards [D.regular_neighborhood p hz hreg] with w hw
  exact D.right_eq p w hw.1 hw.2

theorem difference_zero_real_periods (D : CommonPrincipalPartDisks X)
    (hL : D.difference.ZeroRealAvoidingPeriods D.polesᶜ D.left)
    (hR : D.difference.ZeroRealAvoidingPeriods D.polesᶜ D.right) :
    D.difference.ZeroRealAvoidingPeriods D.polesᶜ D.difference.coefficient := by
  have hsub := HolomorphicCoefficientDisks.zeroRealAvoidingPeriods_sub
    (fun p z hz hr => D.left_continuousAt_regular p hz hr)
    (fun p z hz hr => D.right_continuousAt_regular p hz hr) hL hR
  intro x c
  have he : c.integral D.difference.coefficient = c.integral (fun p z => D.left p z-D.right p z) := by
    apply c.integral_congr
    intro p z hz hr
    rw [D.left_eq p z hz hr,D.right_eq p z hz hr]
    change D.regularLeft p z-D.regularRight p z = _
    ring
  rw [he]
  exact hsub x c

/-- Real-normalized meromorphic differentials with identical Laurent principal
parts agree on their regular locus on any compact connected complex curve.
All period hypotheses concern actual paths avoiding the finite pole set. -/
theorem coefficients_equal [CompactSpace X] [PreconnectedSpace X]
    (D : CommonPrincipalPartDisks X)
    (hL : D.difference.ZeroRealAvoidingPeriods D.polesᶜ D.left)
    (hR : D.difference.ZeroRealAvoidingPeriods D.polesᶜ D.right)
    (p : X) {z : ℂ} (hz : z ∈ ball (chartAt ℂ p p) (D.radius p))
    (hreg : (chartAt ℂ p).symm z ∉ D.poles) : D.left p z = D.right p z := by
  have h0 := HolomorphicCoefficientDisks.zero_of_real_periods_avoiding_finite_poles
    D.poles_finite (D.difference_zero_real_periods hL hR) p hz
  change D.regularLeft p z-D.regularRight p z = 0 at h0
  rw [D.left_eq p z hz hreg,D.right_eq p z hz hreg,sub_eq_zero.mp h0]

/-- Equality also holds as punctured germs at every point, including poles. -/
theorem germs_equal [CompactSpace X] [PreconnectedSpace X]
    (D : CommonPrincipalPartDisks X)
    (hL : D.difference.ZeroRealAvoidingPeriods D.polesᶜ D.left)
    (hR : D.difference.ZeroRealAvoidingPeriods D.polesᶜ D.right) (p : X) :
    D.left p =ᶠ[𝓝[≠] (chartAt ℂ p p)] D.right p := by
  let Q := HolomorphicCoefficientDisks.chartPoles D.poles p \ {chartAt ℂ p p}
  have hQ : Q.Finite := (HolomorphicCoefficientDisks.chartPoles_finite D.poles_finite p).sdiff
  have hn : (chartAt ℂ p p) ∈ Qᶜ := by simp [Q]
  filter_upwards [nhdsWithin_le_nhds (isOpen_ball.mem_nhds (mem_ball_self (D.radius_pos p))),
    nhdsWithin_le_nhds (hQ.isClosed.isOpen_compl.mem_nhds hn),self_mem_nhdsWithin]
    with z hz hzQ hz0
  apply D.coefficients_equal hL hR p hz
  apply (D.difference.chart_regular_iff D.poles p hz).mpr
  intro h
  exact hzQ ⟨h,hz0⟩

end CommonPrincipalPartDisks
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.CommonPrincipalPartDisks.coefficients_equal
#print axioms TwoAxisHelicoid.CommonPrincipalPartDisks.germs_equal
