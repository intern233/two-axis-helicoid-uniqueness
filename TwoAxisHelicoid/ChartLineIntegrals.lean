import TwoAxisHelicoid.HolomorphicPeriodNormalization
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Topology.Path

namespace TwoAxisHelicoid
open Complex Set Metric
open scoped unitInterval
set_option maxHeartbeats 800000

namespace HolomorphicCoefficientDisks
variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

noncomputable def chartSegment (p x y : X) : ℝ → ℂ :=
  AffineMap.lineMap (k := ℝ) (chartAt ℂ p x) (chartAt ℂ p y)

theorem chartSegment_mem (A : HolomorphicCoefficientDisks X) (p : X) {x y : X}
    (hx : x ∈ A.primitives.domain p) (hy : y ∈ A.primitives.domain p)
    {s : ℝ} (hs : s ∈ Icc 0 1) :
    chartSegment p x y s ∈ ball (chartAt ℂ p p) (A.radius p) :=
  (convex_ball _ _).lineMap_mem hx.2 hy.2 hs

/-- The actual path on the surface obtained by lifting a straight segment
inside a coordinate disk. -/
noncomputable def segmentPath (A : HolomorphicCoefficientDisks X) (p : X) {x y : X}
    (hx : x ∈ A.primitives.domain p) (hy : y ∈ A.primitives.domain p) : Path x y where
  toFun s := (chartAt ℂ p).symm (chartSegment p x y s)
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro s
    have h := ((chartAt ℂ p).symm.continuousAt
      (A.ball_target p (A.chartSegment_mem p hx hy s.property))).comp
      (show ContinuousAt (chartSegment p x y) (s : ℝ) from
        AffineMap.lineMap_continuous.continuousAt)
    exact h.comp continuous_subtype_val.continuousAt
  source' := by
    change (chartAt ℂ p).symm (chartSegment p x y (0 : ℝ)) = x
    simpa only [chartSegment,AffineMap.lineMap_apply_zero] using
      (chartAt ℂ p).left_inv hx.1
  target' := by
    change (chartAt ℂ p).symm (chartSegment p x y (1 : ℝ)) = y
    simpa only [chartSegment,AffineMap.lineMap_apply_one] using
      (chartAt ℂ p).left_inv hy.1

/-- Ordinary interval integral of a holomorphic differential along this
coordinate segment, including the derivative of the path. -/
noncomputable def segmentIntegral (A : HolomorphicCoefficientDisks X) (p x y : X) : ℂ :=
  ∫ s : ℝ in 0..1,
    (chartAt ℂ p y-chartAt ℂ p x)*A.coefficient p (chartSegment p x y s)

theorem segmentIntegral_eq (A : HolomorphicCoefficientDisks X) (p : X) {x y : X}
    (hx : x ∈ A.primitives.domain p) (hy : y ∈ A.primitives.domain p) :
    A.segmentIntegral p x y = A.localIntegral p (chartAt ℂ p y)-
      A.localIntegral p (chartAt ℂ p x) := by
  have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :=
    (A.localIntegral_hasDerivAt p (A.chartSegment_mem p hx hy hs)).scomp s
      (AffineMap.hasDerivAt_lineMap (𝕜 := ℝ)
        (a := chartAt ℂ p x) (b := chartAt ℂ p y) (x := s))
  have hc : ContinuousOn (fun s : ℝ =>
      (chartAt ℂ p y-chartAt ℂ p x)*A.coefficient p (chartSegment p x y s)) (Icc 0 1) := by
    intro s hs
    exact (continuousAt_const.mul
      ((A.analytic p _ (A.chartSegment_mem p hx hy hs)).continuousAt.comp
        AffineMap.lineMap_continuous.continuousAt)).continuousWithinAt
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hd s (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs))
    (hc.intervalIntegrable_of_Icc (by norm_num))
  simpa only [segmentIntegral,chartSegment,Function.comp_def,smul_eq_mul,
    AffineMap.lineMap_apply_one,AffineMap.lineMap_apply_zero] using! hi

/-- A finite path made of actual coordinate segments, carrying its complex
line integral. Unlike a relation in `Prop`, this retains the underlying path. -/
inductive IntegralChain (A : HolomorphicCoefficientDisks X) : X → X → ℂ → Type _
  | refl (x : X) : IntegralChain A x x 0
  | step (p x y : X) (hx : x ∈ A.primitives.domain p) (hy : y ∈ A.primitives.domain p) :
      IntegralChain A x y (A.segmentIntegral p x y)
  | trans {x y z : X} {r s : ℂ} :
      IntegralChain A x y r → IntegralChain A y z s → IntegralChain A x z (r+s)

noncomputable def IntegralChain.path {A : HolomorphicCoefficientDisks X}
    {x y : X} {r : ℂ} (c : A.IntegralChain x y r) : Path x y :=
  match c with
  | .refl x => Path.refl x
  | .step p _ _ hx hy => A.segmentPath p hx hy
  | .trans c d => c.path.trans d.path

theorem chain_lifts_to_integrals {A : HolomorphicCoefficientDisks X}
    {x y : X} {r : ℝ} (h : A.primitives.Chain x y r) :
    ∃ c : ℂ, Nonempty (A.IntegralChain x y c) ∧ c.re = r := by
  induction h with
  | refl x => exact ⟨0,⟨IntegralChain.refl x⟩,rfl⟩
  | step p x y hx hy =>
      refine ⟨A.segmentIntegral p x y,⟨IntegralChain.step p x y hx hy⟩,?_⟩
      rw [A.segmentIntegral_eq p hx hy]
      rfl
  | trans h₁ h₂ ih₁ ih₂ =>
      obtain ⟨c,⟨hc⟩,hr⟩ := ih₁
      obtain ⟨d,⟨hd⟩,hs⟩ := ih₂
      exact ⟨c+d,⟨IntegralChain.trans hc hd⟩,by simp only [add_re,hr,hs]⟩

/-- Vanishing real periods of actual piecewise coordinate-linear closed paths. -/
def ZeroRealLinePeriods (A : HolomorphicCoefficientDisks X) : Prop :=
  ∀ x c, A.IntegralChain x x c → c.re = 0

theorem zeroRealPeriods_of_linePeriods {A : HolomorphicCoefficientDisks X}
    (h : A.ZeroRealLinePeriods) : A.ZeroRealPeriods := by
  intro x r hr
  obtain ⟨c,⟨hc⟩,he⟩ := chain_lifts_to_integrals hr
  exact he.symm.trans (h x c hc)

/-- On a compact connected complex curve, holomorphic coefficients with zero
real integrals on these actual closed paths vanish. -/
theorem zero_of_zero_real_line_periods [CompactSpace X] [PreconnectedSpace X]
    {A : HolomorphicCoefficientDisks X} (h : A.ZeroRealLinePeriods) (p : X) :
    A.coefficient p (chartAt ℂ p p) = 0 :=
  zero_of_zero_real_periods (zeroRealPeriods_of_linePeriods h) p

end HolomorphicCoefficientDisks
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.HolomorphicCoefficientDisks.segmentIntegral_eq
#print axioms TwoAxisHelicoid.HolomorphicCoefficientDisks.zero_of_zero_real_line_periods
