import TwoAxisHelicoid.HarmonicComplexCoefficient
import TwoAxisHelicoid.PuncturedLatticePlane
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace TwoAxisHelicoid
open Complex Set MeasureTheory

/-- A parametrized arc in the plane, continuous on its closed parameter
interval and continuously differentiable in its interior with continuous
one-sided velocities up to the endpoints. -/
structure ComplexPeriodArc (Ω : Set ℂ) where
  left : ℝ
  right : ℝ
  ordered : left ≤ right
  curve : ℝ → ℂ
  velocity : ℝ → ℂ
  stays : MapsTo curve (Icc left right) Ω
  continuous_curve : ContinuousOn curve (Icc left right)
  continuous_velocity : ContinuousOn velocity (Icc left right)
  derivative : ∀ s ∈ Ioo left right, HasDerivAt curve (velocity s) s

noncomputable def ComplexPeriodArc.integral {Ω : Set ℂ} (a : ComplexPeriodArc Ω) (f : ℂ → ℂ) : ℂ :=
  ∫ s in a.left..a.right, a.velocity s*f (a.curve s)

theorem ComplexPeriodArc.integral_re_eq_sub {Ω : Set ℂ} (a : ComplexPeriodArc Ω)
    {f : ℂ → ℂ} {X : ℂ → ℝ} (hf : ContinuousOn f Ω)
    (hX : ∀ z ∈ Ω, HasFDerivAt X (realCoefficientDerivative (f z)) z) :
    (a.integral f).re = X (a.curve a.right)-X (a.curve a.left) := by
  have hc := a.continuous_velocity.mul (hf.comp a.continuous_curve a.stays)
  have hi : IntervalIntegrable (fun s => a.velocity s*f (a.curve s)) volume a.left a.right :=
    hc.intervalIntegrable_of_Icc a.ordered
  have he : (a.integral f).re = ∫ s in a.left..a.right, (a.velocity s*f (a.curve s)).re :=
    (Complex.reCLM.intervalIntegral_comp_comm hi).symm
  rw [he]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le a.ordered
    ((show ContinuousOn X Ω from fun z hz => (hX z hz).continuousAt.continuousWithinAt
      ).comp a.continuous_curve a.stays)
  · intro s hs
    exact (hX _ (a.stays (Ioo_subset_Icc_self hs))).comp_hasDerivAt s (a.derivative s hs)
  · exact (Complex.continuous_re.continuousOn.comp hc (mapsTo_univ _ _)).intervalIntegrable_of_Icc a.ordered

/-- Every edge carries its parameter interval and velocity. Concatenations
retain corners, including corners at the base point of a closed curve. -/
inductive PiecewiseComplexPath (Ω : Set ℂ) : ℂ → ℂ → Type
  | refl (z : ℂ) (hz : z ∈ Ω) : PiecewiseComplexPath Ω z z
  | arc (a : ComplexPeriodArc Ω) : PiecewiseComplexPath Ω (a.curve a.left) (a.curve a.right)
  | trans {x y z : ℂ} : PiecewiseComplexPath Ω x y → PiecewiseComplexPath Ω y z → PiecewiseComplexPath Ω x z

noncomputable def PiecewiseComplexPath.integral {Ω : Set ℂ} {x y : ℂ} (p : PiecewiseComplexPath Ω x y)
    (f : ℂ → ℂ) : ℂ :=
  match p with
  | .refl _ _ => 0
  | .arc a => a.integral f
  | .trans p q => p.integral f+q.integral f

theorem PiecewiseComplexPath.integral_re_eq_sub {Ω : Set ℂ} {x y : ℂ} (p : PiecewiseComplexPath Ω x y)
    {f : ℂ → ℂ} {X : ℂ → ℝ} (hf : ContinuousOn f Ω)
    (hX : ∀ z ∈ Ω, HasFDerivAt X (realCoefficientDerivative (f z)) z) :
    (p.integral f).re = X y-X x := by
  induction p with
  | refl => simp [PiecewiseComplexPath.integral]
  | arc a => exact a.integral_re_eq_sub hf hX
  | trans p q hp hq => simp only [PiecewiseComplexPath.integral,add_re,hp,hq]; ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.PiecewiseComplexPath.integral_re_eq_sub
