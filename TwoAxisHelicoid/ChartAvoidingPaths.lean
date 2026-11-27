import TwoAxisHelicoid.ChartLineIntegrals

namespace TwoAxisHelicoid
open Complex Set Metric
open scoped unitInterval
set_option maxHeartbeats 800000

namespace HolomorphicCoefficientDisks
variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- A finite, actual piecewise coordinate-linear path contained in `U`.
Its shape is independent of the differential being integrated. -/
inductive AvoidingPath (A : HolomorphicCoefficientDisks X) (U : Set X) : X → X → Type _
  | refl (x : X) (hx : x ∈ U) : AvoidingPath A U x x
  | step (p x y : X) (hx : x ∈ A.primitives.domain p) (hy : y ∈ A.primitives.domain p)
      (hU : ∀ s : ℝ, s ∈ Icc 0 1 →
        (chartAt ℂ p).symm (chartSegment p x y s) ∈ U) : AvoidingPath A U x y
  | trans {x y z : X} : AvoidingPath A U x y → AvoidingPath A U y z → AvoidingPath A U x z

noncomputable def AvoidingPath.path {A : HolomorphicCoefficientDisks X} {U : Set X}
    {x y : X} (c : A.AvoidingPath U x y) : Path x y :=
  match c with
  | .refl x _ => Path.refl x
  | .step p _ _ hx hy _ => A.segmentPath p hx hy
  | .trans c d => c.path.trans d.path

/-- Line integration with the derivative of each coordinate segment, summed
under concatenation. This is defined for arbitrary local coefficients. -/
noncomputable def AvoidingPath.integral {A : HolomorphicCoefficientDisks X} {U : Set X}
    {x y : X} (c : A.AvoidingPath U x y) (F : X → ℂ → ℂ) : ℂ :=
  match c with
  | .refl _ _ => 0
  | .step p x y _ _ _ => ∫ s : ℝ in 0..1,
      (chartAt ℂ p y-chartAt ℂ p x)*F p (chartSegment p x y s)
  | .trans c d => c.integral F+d.integral F

theorem AvoidingPath.integral_congr {A : HolomorphicCoefficientDisks X} {U : Set X}
    {x y : X} (c : A.AvoidingPath U x y) {F G : X → ℂ → ℂ}
    (h : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) →
      (chartAt ℂ p).symm z ∈ U → F p z = G p z) : c.integral F = c.integral G := by
  induction c with
  | refl => rfl
  | step p x y hx hy hU =>
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
      dsimp only
      rw [h p _ (A.chartSegment_mem p hx hy hs) (hU s hs)]
  | trans c d hc hd => exact congrArg₂ (·+·) hc hd

theorem segment_coefficient_integrable {A : HolomorphicCoefficientDisks X} {U : Set X}
    {F : X → ℂ → ℂ}
    (hF : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) →
      (chartAt ℂ p).symm z ∈ U → ContinuousAt (F p) z)
    (p : X) {x y : X} (hx : x ∈ A.primitives.domain p) (hy : y ∈ A.primitives.domain p)
    (hU : ∀ s : ℝ, s ∈ Icc 0 1 → (chartAt ℂ p).symm (chartSegment p x y s) ∈ U) :
    IntervalIntegrable (fun s : ℝ =>
      (chartAt ℂ p y-chartAt ℂ p x)*F p (chartSegment p x y s)) MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  intro s hs
  exact (continuousAt_const.mul
    ((hF p _ (A.chartSegment_mem p hx hy hs) (hU s hs)).comp
      (show ContinuousAt (chartSegment p x y) s from
        AffineMap.lineMap_continuous.continuousAt))).continuousWithinAt

theorem AvoidingPath.integral_sub {A : HolomorphicCoefficientDisks X} {U : Set X}
    {x y : X} (c : A.AvoidingPath U x y) {F G : X → ℂ → ℂ}
    (hF : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) →
      (chartAt ℂ p).symm z ∈ U → ContinuousAt (F p) z)
    (hG : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) →
      (chartAt ℂ p).symm z ∈ U → ContinuousAt (G p) z) :
    c.integral (fun p z => F p z-G p z) = c.integral F-c.integral G := by
  induction c with
  | refl => simp only [integral,sub_self]
  | step p x y hx hy hU =>
      simp only [integral,mul_sub]
      exact intervalIntegral.integral_sub
        (segment_coefficient_integrable hF p hx hy hU)
        (segment_coefficient_integrable hG p hx hy hU)
  | trans c d hc hd =>
      simp only [integral,hc,hd]
      ring

/-- The ordinary real-period condition on all of the above closed paths. -/
def ZeroRealAvoidingPeriods (A : HolomorphicCoefficientDisks X) (U : Set X)
    (F : X → ℂ → ℂ) : Prop :=
  ∀ x : X, ∀ c : A.AvoidingPath U x x, (c.integral F).re = 0

theorem zeroRealAvoidingPeriods_sub {A : HolomorphicCoefficientDisks X} {U : Set X}
    {F G : X → ℂ → ℂ}
    (hF : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) →
      (chartAt ℂ p).symm z ∈ U → ContinuousAt (F p) z)
    (hG : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) →
      (chartAt ℂ p).symm z ∈ U → ContinuousAt (G p) z)
    (hPF : A.ZeroRealAvoidingPeriods U F) (hPG : A.ZeroRealAvoidingPeriods U G) :
    A.ZeroRealAvoidingPeriods U (fun p z => F p z-G p z) := by
  intro x c
  rw [c.integral_sub hF hG,sub_re,hPF x c,hPG x c,sub_self]

end HolomorphicCoefficientDisks
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.HolomorphicCoefficientDisks.zeroRealAvoidingPeriods_sub
