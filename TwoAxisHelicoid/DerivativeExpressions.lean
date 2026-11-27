import TwoAxisHelicoid.ThetaACurveDerivative
import TwoAxisHelicoid.DyadicInputList

namespace TwoAxisHelicoid
open Complex
attribute [local irreducible] thetaJet thetaA thetaQuotient

noncomputable def thetaGt (t a : ℝ) : ℂ :=
  (Real.pi^3/32 : ℂ)*(2*thetaQuotient t 1 (Real.pi*a/2)*
    (thetaQuotient t 3 (Real.pi*a/2)-thetaQuotient t 1 (Real.pi*a/2)*thetaQuotient t 2 (Real.pi*a/2))-
    (thetaQuotient t 4 (Real.pi*a/2)-(thetaQuotient t 2 (Real.pi*a/2))^2))+(Real.pi/t^2 : ℝ)

noncomputable def thetaAa (t a : ℝ) (z : ℂ) : ℂ := thetaA t a z*thetaLa t a z
noncomputable def thetaAtMidline (t a : ℝ) (z : ℂ) : ℂ :=
  thetaA t a z*(thetaLt t a z+(I/2)*thetaLz t a z)

def quotientInputExpression : BallExpression := .div (.input 1) (.input 0)

theorem value_quotientInputExpression (a b : ℂ) :
    quotientInputExpression.value (complexInputList [a,b]) = b/a := by
  simp [quotientInputExpression, BallExpression.value, complexInputList]

def thetaGtExpression : BallExpression :=
  let r := BallExpression.div (.input 2) (.input 1)
  let u2 := BallExpression.div (.input 3) (.input 1)
  let u3 := BallExpression.div (.input 4) (.input 1)
  let u4 := BallExpression.div (.input 5) (.input 1)
  .add (.mul (.mul (.pow .pi 3) (.rational (1/32)))
    (.sub (.mul (.mul (.rational 2) r) (.sub u3 (.mul r u2))) (.sub u4 (.pow u2 2))))
    (.div .pi (.pow (.input 0) 2))

theorem value_thetaGtExpression (t a : ℝ) :
    thetaGtExpression.value (complexInputList [t,thetaJet t 0 (Real.pi*a/2),
      thetaJet t 1 (Real.pi*a/2),thetaJet t 2 (Real.pi*a/2),thetaJet t 3 (Real.pi*a/2),
      thetaJet t 4 (Real.pi*a/2)]) = thetaGt t a := by
  simp only [thetaGtExpression, BallExpression.value_pow, BallExpression.value_div, BallExpression.value_sub,
    BallExpression.value_rational, BallExpression.value, complexInputList, thetaGt, thetaQuotient,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat,
    Complex.ofReal_div, Complex.ofReal_pow]
  ring

def derivativeLaExpression : BallExpression :=
  .mul .pi (.sub (.sub (.div (.input 3) (.input 2)) (.div (.input 7) (.input 6))) (.input 9))

def derivativeLtExpression : BallExpression :=
  let rz := BallExpression.div (.input 3) (.input 2)
  let u2z := BallExpression.div (.input 4) (.input 2)
  let u3z := BallExpression.div (.input 5) (.input 2)
  let u2m := BallExpression.div (.input 8) (.input 6)
  .add (.mul (.mul .pi (.rational (1/4))) (.sub (.add (.sub (.input 11) (.input 10)) u2m) u2z))
    (.mul (.mul (.mul (.sub (.input 0) (.rational 1)) (.pow .pi 2)) (.rational (1/8)))
      (.sub u3z (.mul rz u2z)))

def derivativeLzExpression : BallExpression :=
  let rz := BallExpression.div (.input 3) (.input 2)
  let rm := BallExpression.div (.input 7) (.input 6)
  let u2z := BallExpression.div (.input 4) (.input 2)
  .add (.mul .pi (.sub rm rz))
    (.mul (.mul (.mul (.sub (.input 0) (.rational 1)) (.pow .pi 2)) (.rational (1/2)))
      (.sub u2z (.pow rz 2)))

def derivativeAaExpression : BallExpression := .mul (.input 1) derivativeLaExpression
def derivativeAtExpression : BallExpression := .mul (.input 1)
  (.add derivativeLtExpression (.mul (.const ⟨0,1/2⟩) derivativeLzExpression))

noncomputable def derivativeValues (t a : ℝ) (z : ℂ) : List ℂ :=
  [a, thetaA t a z, thetaJet t 0 (Real.pi*z/2), thetaJet t 1 (Real.pi*z/2),
    thetaJet t 2 (Real.pi*z/2), thetaJet t 3 (Real.pi*z/2),
    thetaJet t 0 (Real.pi*(z-a)/2), thetaJet t 1 (Real.pi*(z-a)/2),
    thetaJet t 2 (Real.pi*(z-a)/2), thetaQuotient t 1 (Real.pi*a/2),
    thetaQuotient t 2 (Real.pi*a/2), thetaJet t 3 0/thetaJet t 1 0]

theorem value_derivativeAaExpression (t a : ℝ) (z : ℂ) :
    derivativeAaExpression.value (complexInputList (derivativeValues t a z)) = thetaAa t a z := by
  simp [derivativeAaExpression, derivativeLaExpression, BallExpression.value, complexInputList,
    derivativeValues, thetaAa, thetaLa, thetaQuotient]

theorem value_derivativeAtExpression (t a : ℝ) (z : ℂ) :
    derivativeAtExpression.value (complexInputList (derivativeValues t a z)) = thetaAtMidline t a z := by
  simp only [derivativeAtExpression, derivativeLtExpression, derivativeLzExpression, BallExpression.value_pow,
    BallExpression.value_div, BallExpression.value_sub, BallExpression.value_rational, BallExpression.value,
    complexInputList, derivativeValues, thetaAtMidline, thetaLt, thetaLz, thetaQuotient, QComplex.val,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Rat.cast_div, Rat.cast_one, Rat.cast_zero,
    Rat.cast_ofNat]
  have hi : (⟨0,(1/2 : ℝ)⟩ : ℂ) = I/2 := by
    apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im]
  rw [hi]
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.value_derivativeAtExpression
