import TwoAxisHelicoid.TorusHolomorphicLifts

namespace TwoAxisHelicoid
open Complex Set

theorem entire_complex_lattice_increments_affine (L : PeriodPair) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hinc : ∀ ω ∈ L.lattice, ∃ v : ℂ, ∀ z, f (z+ω) = f z+v) :
    ∃ c d : ℂ, ∀ z, f z = c*z+d := by
  have hp (z ω : ℂ) (hω : ω ∈ L.lattice) : deriv f (z+ω) = deriv f z := by
    obtain ⟨v,hv⟩ := hinc ω hω
    have h₁ := (hf (z+ω)).hasDerivAt.comp z ((hasDerivAt_id z).add_const ω)
    have h₂ := (hf z).hasDerivAt.add_const v
    have he : (fun z => f (z+ω)) = (fun z => f z+v) := funext hv
    simp only [Function.comp_def,id_eq,mul_one] at h₁
    rw [he] at h₁
    exact h₁.unique h₂
  have hdf : Differentiable ℂ (deriv f) := fun z => (hf.analyticAt z).deriv.differentiableAt
  let c := deriv f 0
  have hd (z : ℂ) : deriv f z = c := entire_lattice_periodic_constant L hdf hp z 0
  obtain ⟨d,he⟩ := isOpen_univ.exists_eq_add_of_deriv_eq (f := f) (g := fun z : ℂ => c*z) isPreconnected_univ
    hf.differentiableOn (differentiable_id.const_mul c).differentiableOn
    (fun z _ => by rw [deriv_const_mul_id]; exact hd z)
  exact ⟨c,d,fun z => he (mem_univ z)⟩

end TwoAxisHelicoid
