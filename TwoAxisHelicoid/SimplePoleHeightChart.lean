import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.Basic

namespace TwoAxisHelicoid
open Complex Filter
open scoped Topology

noncomputable def simplePoleCoordinate (A : ℂ) (r : ℂ → ℂ) (z : ℂ) : ℂ := A/z+r z
noncomputable def simplePoleReciprocal (A : ℂ) (r : ℂ → ℂ) (z : ℂ) : ℂ := z/(A+z*r z)

@[simp] theorem simplePoleReciprocal_zero (A : ℂ) (r : ℂ → ℂ) :
    simplePoleReciprocal A r 0 = 0 := by simp [simplePoleReciprocal]

theorem simplePoleReciprocal_eq_inv (A : ℂ) (r : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    simplePoleReciprocal A r z = (simplePoleCoordinate A r z)⁻¹ := by
  have he : A/z+r z = (A+z*r z)/z := by field_simp
  simp only [simplePoleReciprocal,simplePoleCoordinate,he,inv_div]

theorem simplePoleReciprocal_analyticAt {A : ℂ} (hA : A ≠ 0)
    {r : ℂ → ℂ} (hr : AnalyticAt ℂ r 0) : AnalyticAt ℂ (simplePoleReciprocal A r) 0 :=
  analyticAt_id.div (analyticAt_const.add (analyticAt_id.mul hr)) (by simpa using hA)

theorem simplePoleReciprocal_hasDerivAt {A : ℂ} (hA : A ≠ 0)
    {r : ℂ → ℂ} (hr : AnalyticAt ℂ r 0) :
    HasDerivAt (simplePoleReciprocal A r) A⁻¹ 0 := by
  have hd := (hasDerivAt_id (0 : ℂ)).div
    (((hasDerivAt_id (0 : ℂ)).mul hr.differentiableAt.hasDerivAt).const_add A)
    (by simpa using hA)
  convert hd using 1
  · rfl
  · simp only [Pi.mul_apply,id_eq,zero_mul,add_zero,one_mul,sub_zero]
    field_simp

theorem simplePoleReciprocal_local_inverse {A : ℂ} (hA : A ≠ 0)
    {r : ℂ → ℂ} (hr : AnalyticAt ℂ r 0) :
    ∃ k : ℂ → ℂ, AnalyticAt ℂ k 0 ∧ k 0 = 0 ∧ HasDerivAt k A 0 ∧
      (∀ᶠ z in 𝓝 (0 : ℂ), k (simplePoleReciprocal A r z) = z) ∧
      (∀ᶠ w in 𝓝 (0 : ℂ), simplePoleReciprocal A r (k w) = w) := by
  have hv := simplePoleReciprocal_analyticAt hA hr
  have hd := simplePoleReciprocal_hasDerivAt hA hr
  have hn : deriv (simplePoleReciprocal A r) 0 ≠ 0 := by rw [hd.deriv]; exact inv_ne_zero hA
  let k := hv.hasStrictDerivAt.localInverse _ _ _ hn
  have hka : AnalyticAt ℂ k 0 := by simpa using hv.analyticAt_localInverse hn
  have hkl : ∀ᶠ z in 𝓝 (0 : ℂ), k (simplePoleReciprocal A r z) = z :=
    hv.hasStrictDerivAt.eventually_left_inverse hn
  have hkr : ∀ᶠ w in 𝓝 (0 : ℂ), simplePoleReciprocal A r (k w) = w := by
    simpa using hv.hasStrictDerivAt.eventually_right_inverse hn
  have hk0 : k 0 = 0 := by simpa using hkl.self_of_nhds
  have hkd : HasDerivAt k A 0 := by
    simpa [hd.deriv] using (hv.hasStrictDerivAt.to_localInverse hn).hasDerivAt
  exact ⟨k,hka,hk0,hkd,hkl,hkr⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.simplePoleReciprocal_local_inverse
