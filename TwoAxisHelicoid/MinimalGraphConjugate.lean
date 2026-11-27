import TwoAxisHelicoid.DirectionalSpinFrame
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace TwoAxisHelicoid
open Complex Filter Set
open scoped Topology ContDiff

/-- Coefficients of the conjugate differential of the horizontal coordinate
on a graph with slopes p and q, in its original real graph coordinates. -/
noncomputable def graphAreaWeight (p q : ℝ) := Real.sqrt (1+p^2+q^2)
noncomputable def graphConjugateA (p q : ℝ) := p*q/graphAreaWeight p q
noncomputable def graphConjugateB (p q : ℝ) := (1+q^2)/graphAreaWeight p q

theorem graphAreaWeight_pos (p q : ℝ) : 0 < graphAreaWeight p q :=
  Real.sqrt_pos.mpr (by positivity)
theorem graphAreaWeight_sq (p q : ℝ) : (graphAreaWeight p q)^2 = 1+p^2+q^2 :=
  Real.sq_sqrt (by positivity)
theorem graphConjugateB_pos (p q : ℝ) : 0 < graphConjugateB p q :=
  div_pos (by positivity) (graphAreaWeight_pos _ _)

noncomputable def graphConjugateForm (p q : ℂ → ℝ) (z : ℂ) : ℂ →L[ℝ] ℝ :=
  graphConjugateA (p z) (q z) • reCLM + graphConjugateB (p z) (q z) • imCLM

theorem graphAreaWeight_deriv {p q : ℝ → ℝ} {a b t : ℝ}
    (hp : HasDerivAt p a t) (hq : HasDerivAt q b t) :
    HasDerivAt (fun s => graphAreaWeight (p s) (q s))
      ((p t*a+q t*b)/graphAreaWeight (p t) (q t)) t := by
  have hn : 1+p t^2+q t^2 ≠ 0 := ne_of_gt (by positivity)
  convert! (((hp.pow 2).const_add 1).add (hq.pow 2)).sqrt hn using 1
  simp only [graphAreaWeight,Pi.add_apply,Pi.pow_apply]
  ring

theorem graphConjugateA_deriv {p q : ℝ → ℝ} {a b t : ℝ}
    (hp : HasDerivAt p a t) (hq : HasDerivAt q b t) :
    HasDerivAt (fun s => graphConjugateA (p s) (q s))
      (((a*q t+p t*b)*graphAreaWeight (p t) (q t) -
        p t*q t*((p t*a+q t*b)/graphAreaWeight (p t) (q t))) /
        graphAreaWeight (p t) (q t)^2) t := by
  exact (hp.mul hq).div (graphAreaWeight_deriv hp hq) (graphAreaWeight_pos _ _).ne'

theorem graphConjugateB_deriv {p q : ℝ → ℝ} {a b t : ℝ}
    (hp : HasDerivAt p a t) (hq : HasDerivAt q b t) :
    HasDerivAt (fun s => graphConjugateB (p s) (q s))
      ((2*q t*b*graphAreaWeight (p t) (q t) -
        (1+q t^2)*((p t*a+q t*b)/graphAreaWeight (p t) (q t))) /
        graphAreaWeight (p t) (q t)^2) t := by
  convert! (((hq.pow 2).const_add 1).div (graphAreaWeight_deriv hp hq) (graphAreaWeight_pos _ _).ne') using 1
  norm_num

theorem graphConjugateForm_smooth {p q : ℂ → ℝ} {n : ℕ∞ω} {z : ℂ}
    (hp : ContDiffAt ℝ n p z) (hq : ContDiffAt ℝ n q z) :
    ContDiffAt ℝ n (graphConjugateForm p q) z := by
  have hD : ContDiffAt ℝ n (fun w => graphAreaWeight (p w) (q w)) z :=
    ((contDiffAt_const.add (hp.pow 2)).add (hq.pow 2)).sqrt (ne_of_gt (by positivity))
  exact (((hp.mul hq).div hD (graphAreaWeight_pos _ _).ne').smul contDiffAt_const).add
    (((contDiffAt_const.add (hq.pow 2)).div hD (graphAreaWeight_pos _ _).ne').smul contDiffAt_const)

end TwoAxisHelicoid
