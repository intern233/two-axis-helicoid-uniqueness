import TwoAxisHelicoid.IntegerAxisGaussPhase
import TwoAxisHelicoid.HarmonicIntegerCoordinateData

namespace TwoAxisHelicoid
open Set Complex
open scoped ComplexConjugate

/-- At an axis point a unit horizontal Gauss direction specifies a vertical plane. -/
def verticalGaussPlane (g : ℂ) : Set (Fin 3 → ℝ) :=
  {v | ∃ r s : ℝ, v = ![r*g.im,-r*g.re,s]}

theorem verticalGaussPlane_neg (g : ℂ) : verticalGaussPlane (-g) = verticalGaussPlane g := by
  ext v
  constructor <;> rintro ⟨r,s,rfl⟩ <;> refine ⟨-r,s,?_⟩ <;>
    simp [Complex.neg_re,Complex.neg_im]

theorem weierstrass_unit_gauss_tangent_range {g h : ℂ} (hg : normSq g = 1) (hh : h ≠ 0) :
    range (nullRealDerivative (weierstrassTriple g h)) = verticalGaussPlane g := by
  have hi : g⁻¹ = conj g := by simp [Complex.inv_def,hg]
  have ht (w : ℂ) : nullRealDerivative (weierstrassTriple g h) w =
      ![(w*h).im*g.im,-(w*h).im*g.re,(w*h).re] := by
    funext j
    fin_cases j <;> simp [weierstrassTriple,hi,Complex.mul_re,Complex.mul_im] <;> ring
  ext v
  constructor
  · rintro ⟨w,rfl⟩
    exact ⟨(w*h).im,(w*h).re,ht w⟩
  · rintro ⟨r,s,rfl⟩
    refine ⟨(⟨s,r⟩ : ℂ)/h,?_⟩
    rw [ht,div_mul_cancel₀ _ hh]

/-- The ruled helicoid with angular speed α and horizontal Gauss
direction g at height b. The parameter's real part runs along a ruling. -/
noncomputable def axisRuledHelicoid (g : ℂ) (α b : ℝ) (w : ℂ) : Fin 3 → ℝ :=
  let v := g * Complex.exp (I*(α*(w.im-b) : ℝ))
  ![w.re*v.im,-w.re*v.re,w.im]

theorem axisRuledHelicoid_tangent_range (g : ℂ) (α b x : ℝ) :
    range (fderiv ℝ (axisRuledHelicoid g α b) (I*x)) =
      verticalGaussPlane (g * Complex.exp (I*(α*(x-b) : ℝ))) := by
  let z := I*(x : ℂ)
  let v := fun w : ℂ => g * Complex.exp (I*(α*(w.im-b) : ℝ))
  have hv : DifferentiableAt ℝ v z := by dsimp [v]; fun_prop
  have hz : z.re = 0 := by simp [z]
  let A := fun w : ℂ => w.re*(v w).im
  let B := fun w : ℂ => -w.re*(v w).re
  have hA := Complex.reCLM.hasFDerivAt.mul
    (Complex.imCLM.hasFDerivAt.comp z hv.hasFDerivAt)
  have hB := Complex.reCLM.hasFDerivAt.neg.mul
    (Complex.reCLM.hasFDerivAt.comp z hv.hasFDerivAt)
  have HD : HasFDerivAt (axisRuledHelicoid g α b)
      (ContinuousLinearMap.pi ![fderiv ℝ A z,fderiv ℝ B z,Complex.imCLM]) z := by
    apply hasFDerivAt_pi.mpr
    intro j
    fin_cases j
    · exact (show HasFDerivAt A _ z from hA).differentiableAt.hasFDerivAt
    · exact (show HasFDerivAt B _ z from hB).differentiableAt.hasFDerivAt
    · exact Complex.imCLM.hasFDerivAt
  have hh (w : ℂ) : fderiv ℝ (axisRuledHelicoid g α b) z w =
      ![w.re*(v z).im,-w.re*(v z).re,w.im] := by
    rw [HD.fderiv]
    funext j
    fin_cases j
    · change fderiv ℝ A z w = _
      rw [(show HasFDerivAt A _ z from hA).fderiv]
      simp [hz,mul_comm]
    · change fderiv ℝ B z w = _
      rw [(show HasFDerivAt B _ z from hB).fderiv]
      simp [hz,mul_comm]
    · rfl
  change range (fderiv ℝ (axisRuledHelicoid g α b) z) = _
  have hvz : v z = g * Complex.exp (I*(α*(x-b) : ℝ)) := by simp [v,z]
  rw [← hvz]
  ext q
  constructor
  · rintro ⟨w,rfl⟩
    exact ⟨_,_,hh w⟩
  · rintro ⟨r,s,rfl⟩
    exact ⟨⟨r,s⟩,hh _⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.axisRuledHelicoid_tangent_range
#print axioms TwoAxisHelicoid.weierstrass_unit_gauss_tangent_range
