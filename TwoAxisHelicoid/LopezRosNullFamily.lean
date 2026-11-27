import TwoAxisHelicoid.LopezRosSingleValuedFamily

namespace TwoAxisHelicoid
open Complex Set InnerProductSpace

noncomputable def lopezRosCoefficients (k : ℂ) (p : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![lopezRosHorizontal k (p 0) (p 1) 0,lopezRosHorizontal k (p 0) (p 1) 1,p 2]

/-- The reciprocal horizontal scaling preserves both the complex null
identity and immersion at every ordinary point, including zeros of the
height differential. -/
theorem lopezRosCoefficients_regular {k : ℂ} (hk : k ≠ 0) {p : Fin 3 → ℂ} (hp : ComplexNull p) (hn : p ≠ 0) :
    ComplexNull (lopezRosCoefficients k p) ∧ lopezRosCoefficients k p ≠ 0 := by
  let q := lopezRosCoefficients k p
  obtain ⟨hh,hl⟩ := lopezRosHorizontal_characteristic k (p 0) (p 1)
  change q 0+I*q 1 = k*(p 0+I*p 1) at hh
  change q 0-I*q 1 = k⁻¹*(p 0-I*p 1) at hl
  have fac (x y : ℂ) : x^2+y^2 = (x+I*y)*(x-I*y) := by linear_combination y^2*I_sq
  have hmul : q 0^2+q 1^2 = p 0^2+p 1^2 := by
    rw [fac,fac (p 0),hh,hl]
    field_simp
  refine ⟨?_,fun h => hn ?_⟩
  · change q 0^2+q 1^2+p 2^2 = 0
    rw [hmul]
    exact hp
  · have h0 : q 0 = 0 := congrFun h 0
    have h1 : q 1 = 0 := congrFun h 1
    rw [h0,h1,mul_zero,add_zero] at hh
    rw [h0,h1,mul_zero,sub_zero] at hl
    have ha := (mul_eq_zero.mp hh.symm).resolve_left hk
    have hb := (mul_eq_zero.mp hl.symm).resolve_left (inv_ne_zero hk)
    have hx : p 0 = 0 := by linear_combination (ha+hb)/2
    have hy : I*p 1 = 0 := by linear_combination (ha-hb)/2
    funext j
    fin_cases j
    · exact hx
    · exact (mul_eq_zero.mp hy).resolve_left I_ne_zero
    · exact congrFun h 2

/-- The closed López–Ros family obtained from a vertical-flux immersion
consists of genuine harmonic conformal immersions on the same punctured
torus for every nonzero multiplier, with their actual derivatives. -/
theorem vertical_flux_lopez_ros_immersions (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (hX : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L X w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L X) z ∧ Function.Injective (fderiv ℝ (puncturedTorusPullback L X) z))
    (hflux : ¬ HasIntrinsicNonverticalFlux L X) :
    ∃ Y : ℂ → PuncturedPeriodTorus L → Fin 3 → ℝ, Y 1 = X ∧ (∀ k q, Y k q 2 = X q 2) ∧
      ∀ k ≠ 0, ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L (Y k) w j) z) ∧
        ConformalCoordinateDerivatives (puncturedTorusPullback L (Y k)) z ∧
        Function.Injective (fderiv ℝ (puncturedTorusPullback L (Y k)) z) ∧
        HasFDerivAt (puncturedTorusPullback L (Y k)) (nullRealDerivative (lopezRosCoefficients k (torusImmersionForms L X z))) z := by
  obtain ⟨Y,hY1,hY2,hY⟩ := vertical_flux_lopez_ros_single_valued_family L X (fun z hz => ⟨(hX z hz).1,(hX z hz).2.1⟩) hflux
  refine ⟨Y,hY1,hY2,fun k hk z hz => ?_⟩
  let p := torusImmersionForms L X z
  let q := lopezRosCoefficients k p
  let Z := puncturedTorusPullback L (Y k)
  have hv : (fun w => Z w 2) = fun w => puncturedTorusPullback L X w 2 := by
    funext w
    by_cases hw : w ∉ L.lattice <;> simp [Z,puncturedTorusPullback,hw,hY2]
  have ha : AnalyticAt ℝ (puncturedTorusPullback L X) z :=
    analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt ((hX z hz).1 j)
  obtain ⟨hqn,hq0⟩ := lopezRosCoefficients_regular hk (immersionComplexCoefficient_null (hX z hz).2.1)
    (immersionComplexCoefficient_regular ha.differentiableAt (hX z hz).2.2)
  have dj (j : Fin 3) : HasFDerivAt (fun w => Z w j) (realCoefficientDerivative (q j)) z ∧ HarmonicAt (fun w => Z w j) z := by
    fin_cases j
    · exact hY k 0 z hz
    · exact hY k 1 z hz
    · change HasFDerivAt (fun w => Z w 2) (realCoefficientDerivative (q 2)) z ∧ HarmonicAt (fun w => Z w 2) z
      rw [hv]
      exact ⟨scalarComplexCoefficient_hasFDerivAt ((_root_.HarmonicAt.analyticAt ((hX z hz).1 2)).differentiableAt),
        (hX z hz).1 2⟩
  have hD : HasFDerivAt Z (nullRealDerivative q) z := by
    convert hasFDerivAt_pi.mpr (fun j => (dj j).1) using 1
    ext v j
    rfl
  have hcomp (j : Fin 3) : fderiv ℝ (fun w => Z w j) z = (ContinuousLinearMap.proj j).comp (nullRealDerivative q) :=
    ((ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp z hD).fderiv
  obtain ⟨_,h1,hI,hortho⟩ := nullRealDerivative_conformal hqn hq0
  refine ⟨fun j => (dj j).2,?_,?_,hD⟩
  · change ConformalCoordinateDerivatives Z z
    unfold ConformalCoordinateDerivatives
    simpa only [hcomp,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply] using! And.intro (h1.trans hI.symm) hortho
  · change Function.Injective (fderiv ℝ Z z)
    rw [hD.fderiv]
    exact nullRealDerivative_injective hqn hq0

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.vertical_flux_lopez_ros_immersions
