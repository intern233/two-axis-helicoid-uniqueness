import TwoAxisHelicoid.ChartLineIntegrals

namespace TwoAxisHelicoid.HolomorphicCoefficientDisks
open Complex Set Metric
open scoped Topology ComplexConjugate
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

private noncomputable def scaled (A : HolomorphicCoefficientDisks M) (c : ℂ) : HolomorphicCoefficientDisks M where
  radius := A.radius
  radius_pos := A.radius_pos
  ball_target := A.ball_target
  coefficient := fun i z => c*A.coefficient i z
  analytic := fun i z hz => analyticAt_const.mul (A.analytic i z hz)

private theorem scaled_segment (A : HolomorphicCoefficientDisks M) (a : ℂ) (p x y : M) :
    (scaled A a).segmentIntegral p x y=a*A.segmentIntegral p x y := by
  unfold segmentIntegral
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  change _*(a*_) = a*(_*_)
  ring

private theorem unscale_integral_chain (A : HolomorphicCoefficientDisks M) (a : ℂ) {x y : M} {r : ℂ}
    (c : (scaled A a).IntegralChain x y r) : ∃ v, Nonempty (A.IntegralChain x y v) ∧ a*v=r := by
  induction c with
  | refl x => exact ⟨0,⟨.refl x⟩,mul_zero a⟩
  | step p x y hx hy => exact ⟨_,⟨.step p x y hx hy⟩,(scaled_segment A a p x y).symm⟩
  | trans q r hq hr =>
    obtain ⟨v,⟨a'⟩,e⟩ := hq
    obtain ⟨w,⟨b'⟩,f⟩ := hr
    exact ⟨v+w,⟨.trans a' b'⟩,by rw [mul_add,e,f]⟩

private theorem reverse_chain {A : HolomorphicCoefficientDisks M} {x y : M} {v : ℂ} (c : A.IntegralChain x y v) :
    Nonempty (A.IntegralChain y x (-v)) := by
  induction c with
  | refl x => simpa only [neg_zero] using (show Nonempty (A.IntegralChain x x 0) from ⟨.refl x⟩)
  | step p x y hx hy =>
    have eq : -A.segmentIntegral p x y=A.segmentIntegral p y x := by
      rw [A.segmentIntegral_eq p hx hy,A.segmentIntegral_eq p hy hx,neg_sub]
    rw [eq]
    exact ⟨.step p y x hy hx⟩
  | trans q r hq hr =>
    obtain ⟨a⟩ := hr
    obtain ⟨b⟩ := hq
    rw [neg_add_rev]
    exact ⟨.trans a b⟩

private theorem move_closed_period [PreconnectedSpace M] (A : HolomorphicCoefficientDisks M) (base : M)
    {x : M} {v : ℂ} (loop : A.IntegralChain x x v) : Nonempty (A.IntegralChain base base v) := by
  obtain ⟨_,ch⟩ := A.primitives.exists_chain base x
  obtain ⟨t,⟨f⟩,_⟩ := chain_lifts_to_integrals ch
  obtain ⟨g⟩ := reverse_chain f
  have join := IntegralChain.trans (IntegralChain.trans f loop) g
  rw [show t+v+ -t=v by abel] at join
  exact ⟨join⟩

/-- No real direction annihilates every period of a nonzero holomorphic
one-form on a compact connected surface. The loops are actual finite
concatenations of coordinate segments at one prescribed base point. -/
theorem based_holomorphic_period_detects_direction [CompactSpace M] [PreconnectedSpace M]
    (A : HolomorphicCoefficientDisks M) (base p : M) (atp : A.coefficient p (chartAt ℂ p p)≠0)
    {a : ℂ} (an : a≠0) : ∃ v : ℂ, Nonempty (A.IntegralChain base base v) ∧ (a*v).re≠0 := by
  by_contra h
  have allZero : (scaled A a).ZeroRealLinePeriods := by
    intro x r c
    obtain ⟨v,⟨loop⟩,eq⟩ := unscale_integral_chain A a c
    rw [← eq]
    exact Classical.byContradiction (fun ne => h ⟨v,move_closed_period A base loop,ne⟩)
  exact (mul_ne_zero an atp) (zero_of_zero_real_line_periods allZero p)

/-- Two closed paths based at the same point have period vectors with
nonzero real determinant. No assumption on the zeros elsewhere, the
period lattice, or the genus enters this conclusion. -/
theorem exists_two_independent_holomorphic_periods [CompactSpace M] [PreconnectedSpace M]
    (A : HolomorphicCoefficientDisks M) (base p : M) (atp : A.coefficient p (chartAt ℂ p p)≠0) :
    ∃ v w : ℂ, Nonempty (A.IntegralChain base base v) ∧ Nonempty (A.IntegralChain base base w) ∧
      v.re*w.im-v.im*w.re≠0 := by
  obtain ⟨v,cv,v₀⟩ := based_holomorphic_period_detects_direction A base p atp (one_ne_zero : (1:ℂ)≠0)
  have vn : v≠0 := fun h => v₀ (by simp [h])
  have nz : -I*conj v≠0 := mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (by simpa using vn)
  obtain ⟨w,cw,hw⟩ := based_holomorphic_period_detects_direction A base p atp nz
  refine ⟨v,w,cv,cw,?_⟩
  have eq : ((-I*conj v)*w).re=v.re*w.im-v.im*w.re := by simp [mul_re,mul_im]
  rwa [eq] at hw

end TwoAxisHelicoid.HolomorphicCoefficientDisks
#print axioms TwoAxisHelicoid.HolomorphicCoefficientDisks.exists_two_independent_holomorphic_periods
