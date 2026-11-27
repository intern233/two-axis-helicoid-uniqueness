import TwoAxisHelicoid.AxisHelicoidGauge
import TwoAxisHelicoid.HolomorphicNullImmersion
import TwoAxisHelicoid.MinimalChartComplexData
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

namespace TwoAxisHelicoid
open Complex Set Function InnerProductSpace
open scoped Topology ContDiff

/-- A global conformal parameter for the unit-pitch comparison helicoid. -/
noncomputable def comparisonHelicoidSheet (z : ℂ) : Fin 3 → ℝ :=
  ![(Complex.sinh z).re,(Complex.cosh z).im,z.im]

private theorem hyperbolic_coordinate_parts (z : ℂ) :
    (Complex.sinh z).re=Real.sinh z.re*Real.cos z.im ∧
    (Complex.cosh z).im=Real.sinh z.re*Real.sin z.im := by
  have parts := Complex.re_add_im z
  constructor
  · calc (Complex.sinh z).re=(Complex.sinh ((z.re:ℂ)+(z.im:ℂ)*I)).re :=
           congrArg (fun w => (Complex.sinh w).re) parts.symm
         _=_ := by
           rw [Complex.sinh_add,Complex.cosh_mul_I,Complex.sinh_mul_I,
             ← Complex.ofReal_sinh,← Complex.ofReal_cosh,← Complex.ofReal_sin,← Complex.ofReal_cos]
           simp [Complex.mul_re,Complex.mul_im]
           rfl
  · calc (Complex.cosh z).im=(Complex.cosh ((z.re:ℂ)+(z.im:ℂ)*I)).im :=
           congrArg (fun w => (Complex.cosh w).im) parts.symm
         _=_ := by
           rw [Complex.cosh_add,Complex.cosh_mul_I,Complex.sinh_mul_I,
             ← Complex.ofReal_sinh,← Complex.ofReal_cosh,← Complex.ofReal_sin,← Complex.ofReal_cos]
           simp [Complex.mul_re,Complex.mul_im]
           rfl

theorem comparisonHelicoidSheet_coordinates (z : ℂ) :
    comparisonHelicoidSheet z=![Real.sinh z.re*Real.cos z.im,Real.sinh z.re*Real.sin z.im,z.im] := by
  obtain ⟨a,b⟩ := hyperbolic_coordinate_parts z
  simp only [comparisonHelicoidSheet,a,b]

/-- The three actual coordinate functions are harmonic, and the differential
is conformal and regular everywhere, including all points on the straight axis. -/
theorem comparisonHelicoidSheet_regular (z : ℂ) :
    (∀ j, HarmonicAt (fun w => comparisonHelicoidSheet w j) z) ∧
    ConformalCoordinateDerivatives comparisonHelicoidSheet z ∧
    Injective (fderiv ℝ comparisonHelicoidSheet z) := by
  let F := fun z : ℂ => (![Complex.sinh z,-I*Complex.cosh z,-I*z] : Fin 3 → ℂ)
  let p : Fin 3 → ℂ := ![Complex.cosh z,-I*Complex.sinh z,-I]
  have dF : HasDerivAt F p z := by
    apply hasDerivAt_pi.mpr
    intro j
    fin_cases j
    · exact Complex.hasDerivAt_sinh z
    · exact (Complex.hasDerivAt_cosh z).const_mul (-I)
    · change HasDerivAt (fun w : ℂ => -I*w) (-I) z
      simpa only [mul_one] using ((hasDerivAt_id' z).const_mul (-I))
  have eq : comparisonHelicoidSheet=coordinateRealPart ∘ F := by
    funext w j
    fin_cases j <;> simp [comparisonHelicoidSheet,F,Complex.mul_re]
  have d := realPart_primitive_hasFDerivAt dF
  have hd : HasFDerivAt comparisonHelicoidSheet (nullRealDerivative p) z := eq.symm ▸ d
  have null : ComplexNull p := by
    change (Complex.cosh z)^2+(-I*Complex.sinh z)^2+(-I)^2=0
    rw [mul_pow,neg_sq,Complex.I_sq]
    linear_combination Complex.cosh_sq_sub_sinh_sq z
  have ne : p≠0 := fun hh => (neg_ne_zero.mpr I_ne_zero) (congrFun hh 2)
  obtain ⟨_,equal₁,equal₂,orth⟩ := nullRealDerivative_conformal null ne
  have coordinates (j : Fin 3) (w : ℂ) : fderiv ℝ (fun u => comparisonHelicoidSheet u j) z w=nullRealDerivative p w j :=
    (fderiv_real_coordinate hd.differentiableAt j w).trans (congrArg (fun D : ℂ →L[ℝ] (Fin 3 → ℝ) => D w j) hd.fderiv)
  refine ⟨?_,?_,hd.fderiv.symm ▸ nullRealDerivative_injective null ne⟩
  · intro j
    fin_cases j
    · exact Complex.analyticAt_sinh.harmonicAt_re
    · exact Complex.analyticAt_cosh.harmonicAt_im
    · exact (analyticAt_id (𝕜:=ℂ) (z:=z)).harmonicAt_im
  · simpa only [ConformalCoordinateDerivatives,coordinates] using And.intro (equal₁.trans equal₂.symm) orth

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.comparisonHelicoidSheet_coordinates
#print axioms TwoAxisHelicoid.comparisonHelicoidSheet_regular
