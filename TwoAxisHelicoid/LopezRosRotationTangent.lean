import TwoAxisHelicoid.IntrinsicLopezRosVariation

namespace TwoAxisHelicoid
open Complex Set InnerProductSpace

/-- The first order change of both complex horizontal coefficients is
exactly the infinitesimal vertical rotation of angular speed Im k'. -/
theorem lopez_ros_rotational_tangent {k : ℝ → ℂ} {d : ℂ} (hk : HasDerivAt k d 0)
    (hk0 : k 0 = 1) (hd : d.re = 0) (x y : ℂ) :
    HasDerivAt (fun s => lopezRosHorizontal (k s) x y 0) (-(d.im:ℂ)*y) 0 ∧
    HasDerivAt (fun s => lopezRosHorizontal (k s) x y 1) ((d.im:ℂ)*x) 0 := by
  have hInv : HasDerivAt (fun s => (k s)⁻¹) (-d) 0 := by
    simpa only [hk0,one_pow,div_one] using! hk.inv (by rw [hk0]; exact one_ne_zero)
  have hA : HasDerivAt (fun s => lopezRosAverage (k s)) 0 0 := by
    simpa only [lopezRosAverage,add_neg_cancel,zero_div] using! (hk.add hInv).div_const 2
  have hb : I*d = -(d.im:ℂ) := by apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,hd]
  have hB : HasDerivAt (fun s => lopezRosSkew (k s)) (I*d) 0 := by
    convert ((hk.sub hInv).const_mul I).div_const 2 using 1
    · rfl
    · ring
  rw [hb] at hB
  constructor
  · simpa only [zero_mul,zero_add] using! (hA.mul_const x).add (hB.mul_const y)
  · simpa only [zero_mul,zero_sub,neg_mul,neg_neg] using! (hA.mul_const y).sub (hB.mul_const x)

/-- A closed López–Ros deformation has exactly one real infinitesimal
degree of freedom, the ordinary vertical rotation. Every purely
imaginary multiplier velocity preserves all periods to first order. -/
theorem lopez_ros_first_order_closure_iff_rotation (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (hX : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L X w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L X) z)
    (hflux : HasIntrinsicNonverticalFlux L X) {k : ℝ → ℂ} {d : ℂ}
    (hk : HasDerivAt k d 0) (hk0 : k 0 = 1) : LopezRosClosedToFirstOrder L X k ↔ d.re = 0 := by
  refine ⟨intrinsic_lopez_ros_velocity_pure_imaginary L X hX hflux hk hk0,?_⟩
  intro hd a b γ hγ j
  let p := torusImmersionForms L X
  obtain ⟨ha,_,hD⟩ := torusImmersionForms_regular L X (fun z hz => (hX z hz).1) (fun z hz => (hX z hz).2)
  have hp (j : Fin 3) : ContinuousOn (fun z => p z j) (L.lattice : Set ℂ)ᶜ :=
    fun z hz => (ha z hz j).continuousAt.continuousWithinAt
  let P := fun j => γ.integral (fun z => p z j)
  have hP (j : Fin 3) : (P j).re = 0 := by
    have h := γ.integral_re_eq_sub (hp j) (X := fun z => torusFilledPosition L X (periodTorusProjection L z) j)
      (fun z hz => (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp z (hD z hz))
    simpa [hγ,P] using h
  change HasDerivAt (fun s => (γ.integral (fun z => lopezRosHorizontal (k s) (p z 0) (p z 1) j)).re) 0 0
  simp only [γ.integral_lopezRosHorizontal (hp 0) (hp 1)]
  obtain ⟨h₀,h₁⟩ := lopez_ros_rotational_tangent hk hk0 hd (P 0) (P 1)
  fin_cases j
  · simpa [Complex.mul_re,hP] using! Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 h₀
  · simpa [Complex.mul_re,hP] using! Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 h₁

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.lopez_ros_first_order_closure_iff_rotation
