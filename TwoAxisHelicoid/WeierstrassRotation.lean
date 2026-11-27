import TwoAxisHelicoid.GaussMultiplierRigidity
import TwoAxisHelicoid.HolomorphicNullImmersion

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

noncomputable def weierstrassTriple (g h : ℂ) : Fin 3 → ℂ :=
  ![(g⁻¹-g)/2*h,I*(g⁻¹+g)/2*h,h]

noncomputable def verticalRotation (c : ℂ) : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi ![
    c.re • ContinuousLinearMap.proj 0-c.im • ContinuousLinearMap.proj 1,
    c.im • ContinuousLinearMap.proj 0+c.re • ContinuousLinearMap.proj 1,
    ContinuousLinearMap.proj 2]

@[simp] theorem verticalRotation_apply (c : ℂ) (v : Fin 3 → ℝ) :
    verticalRotation c v = ![c.re*v 0-c.im*v 1,c.im*v 0+c.re*v 1,v 2] := by
  ext j
  fin_cases j <;> rfl

theorem verticalRotation_preserves_squared_length {c : ℂ} (hc : ‖c‖ = 1)
    (v : Fin 3 → ℝ) : ∑ j, (verticalRotation c v j)^2 = ∑ j, (v j)^2 := by
  have he : c.re^2+c.im^2 = 1 := by
    have h := Complex.normSq_eq_norm_sq c
    rw [hc] at h
    simpa only [Complex.normSq_apply,one_pow,pow_two,one_mul] using h
  rw [verticalRotation_apply]
  simp [Fin.sum_univ_succ]
  linear_combination (v 0^2+v 1^2)*he

theorem weierstrassTriple_unit_multiplier {c : ℂ} (hc : ‖c‖ = 1) (g h : ℂ) :
    weierstrassTriple (c*g) h =
      ![(c.re : ℂ)*weierstrassTriple g h 0-(c.im : ℂ)*weierstrassTriple g h 1,
        (c.im : ℂ)*weierstrassTriple g h 0+(c.re : ℂ)*weierstrassTriple g h 1,
        weierstrassTriple g h 2] := by
  ext j
  fin_cases j <;> dsimp [weierstrassTriple]
  · rw [mul_inv,Complex.inv_eq_conj hc]
    have hrepr : c = (c.re : ℂ)+(c.im : ℂ)*I := (Complex.re_add_im c).symm
    conv_lhs => rw [hrepr]
    simp only [map_add,map_mul,Complex.conj_ofReal,Complex.conj_I]
    ring
  · rw [mul_inv,Complex.inv_eq_conj hc]
    have hrepr : c = (c.re : ℂ)+(c.im : ℂ)*I := (Complex.re_add_im c).symm
    conv_lhs => rw [hrepr]
    simp only [map_add,map_mul,Complex.conj_ofReal,Complex.conj_I]
    ring_nf
    simp only [I_sq]
    ring

theorem nullRealDerivative_unit_multiplier {c : ℂ} (hc : ‖c‖ = 1) (g h : ℂ) :
    nullRealDerivative (weierstrassTriple (c*g) h) =
      (verticalRotation c).comp (nullRealDerivative (weierstrassTriple g h)) := by
  rw [weierstrassTriple_unit_multiplier hc]
  ext w j
  fin_cases j <;>
    simp [verticalRotation_apply,Complex.mul_re,Complex.mul_im] <;> ring

/-- Integrating a unit Gauss multiplier produces a vertical Euclidean rotation
and an additive translation. The differential hypotheses are on the actual
coordinate maps, rather than a formal tuple of periods. -/
theorem weierstrass_primitives_unit_multiplier {s : Set ℂ}
    (hs : IsOpen s) (hconn : IsPreconnected s) {g h : ℂ → ℂ} {c : ℂ}
    (hc : ‖c‖ = 1) {X Y : ℂ → Fin 3 → ℝ}
    (hX : ∀ z ∈ s, HasFDerivAt X (nullRealDerivative (weierstrassTriple (g z) (h z))) z)
    (hY : ∀ z ∈ s, HasFDerivAt Y (nullRealDerivative (weierstrassTriple (c*g z) (h z))) z) :
    ∃ b : Fin 3 → ℝ, ∀ z ∈ s, Y z = verticalRotation c (X z)+b := by
  have hR (z : ℂ) (hz : z ∈ s) := (verticalRotation c).hasFDerivAt.comp z (hX z hz)
  apply hs.exists_eq_add_of_fderiv_eq hconn
    (fun z hz => (hY z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hR z hz).differentiableAt.differentiableWithinAt)
  intro z hz
  rw [(hY z hz).fderiv,(hR z hz).fderiv,nullRealDerivative_unit_multiplier hc]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.weierstrass_primitives_unit_multiplier
