import TwoAxisHelicoid.ThetaCompositeContinuity
import TwoAxisHelicoid.RootVerticalIncreasing

namespace TwoAxisHelicoid
open Set Complex
attribute [local irreducible] thetaJet thetaQuotient

theorem root_quotient_continuousOn (j : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => thetaQuotient p.1 j (Real.pi*p.2/2)) rootRectangle := by
  apply thetaQuotient_comp_continuousOn continuous_fst.continuousOn (by fun_prop)
  · intro p hp
    exact root_t_positive hp.1.1
  · intro p hp
    exact root_vertical_denominator hp.1.1 hp.1.2 hp.2.1 hp.2.2

theorem thetaGa_rootRectangle_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ => thetaGa p.1 p.2) rootRectangle := by
  have h1 := root_quotient_continuousOn 1
  have h2 := root_quotient_continuousOn 2
  have h3 := root_quotient_continuousOn 3
  exact continuousOn_const.mul ((((continuousOn_const.mul h1).mul h2).sub
    (continuousOn_const.mul (h1.pow 3))).sub h3)

theorem thetaGt_rootRectangle_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ => thetaGt p.1 p.2) rootRectangle := by
  have h1 := root_quotient_continuousOn 1
  have h2 := root_quotient_continuousOn 2
  have h3 := root_quotient_continuousOn 3
  have h4 := root_quotient_continuousOn 4
  have hpi : ContinuousOn (fun p : ℝ × ℝ => Real.pi/p.1^2) rootRectangle :=
    continuousOn_const.div (continuous_fst.continuousOn.pow 2)
      (fun p hp => pow_ne_zero 2 (root_t_positive hp.1.1).ne')
  exact (continuousOn_const.mul (((continuousOn_const.mul h1).mul (h3.sub (h1.mul h2))).sub
    (h4.sub (h2.pow 2)))).add (Complex.continuous_ofReal.comp_continuousOn hpi)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaGa_rootRectangle_continuousOn
#print axioms TwoAxisHelicoid.thetaGt_rootRectangle_continuousOn
