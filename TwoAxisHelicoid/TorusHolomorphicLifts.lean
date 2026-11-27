import TwoAxisHelicoid.TorusLinearAutomorphisms
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.Connected.TotallyDisconnected

namespace TwoAxisHelicoid
open Complex Set

def HasLatticeIncrements (L : PeriodPair) (f : ℂ → ℂ) : Prop :=
  ∀ ω ∈ L.lattice, ∃ v ∈ L.lattice, ∀ z, f (z+ω) = f z+v

theorem entire_lattice_periodic_constant (L : PeriodPair) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hp : ∀ z ω, ω ∈ L.lattice → f (z+ω) = f z) (z w : ℂ) : f z = f w := by
  have hb := (IsZLattice.isCompact_range_of_periodic L.lattice f hf.continuous hp).isBounded
  exact hf.apply_eq_apply_of_bounded hb z w

theorem entire_lattice_increment_affine (L : PeriodPair) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hinc : HasLatticeIncrements L f) :
    ∃ c d : ℂ, ∀ z, f z = c*z+d := by
  have hp (z ω : ℂ) (hω : ω ∈ L.lattice) : deriv f (z+ω) = deriv f z := by
    obtain ⟨v,_,hv⟩ := hinc ω hω
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

theorem entire_lattice_increment_fix_zero (L : PeriodPair) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hinc : HasLatticeIncrements L f) (h0 : f 0 = 0) :
    ∃ c : ℂ, (∀ z, f z = c*z) ∧ PreservesPeriodLattice L c := by
  obtain ⟨c,d,he⟩ := entire_lattice_increment_affine L hf hinc
  have hd : d = 0 := by simpa [h0] using (he 0).symm
  have he' (z : ℂ) : f z = c*z := by simpa only [hd,add_zero] using he z
  refine ⟨c,he',?_⟩
  intro ω hω
  obtain ⟨v,hv,heω⟩ := hinc ω hω
  have hx := heω 0
  rw [zero_add,h0,zero_add,he'] at hx
  exact hx ▸ hv

/-- A holomorphic lift of a puncture-fixing torus automorphism, with a
holomorphic inverse lift fixing zero, has a lattice-preserving unit multiplier. -/
theorem torus_holomorphic_inverse_lifts_linear (L : PeriodPair) {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hfi : HasLatticeIncrements L f) (hgi : HasLatticeIncrements L g)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) (hinv : Function.LeftInverse g f) :
    ∃ c : ℂ, PeriodLatticeAutomultiplier L c ∧ ∀ z, f z = c*z := by
  obtain ⟨c,hc,hcL⟩ := entire_lattice_increment_fix_zero L hf hfi hf0
  obtain ⟨d,hd,hdL⟩ := entire_lattice_increment_fix_zero L hg hgi hg0
  have hdc : d*c = 1 := by simpa only [hc,hd,mul_one] using hinv 1
  have hcn : c ≠ 0 := by intro h; simp [h] at hdc
  have hdi : d = c⁻¹ := by
    apply mul_right_cancel₀ hcn
    rw [hdc,inv_mul_cancel₀ hcn]
  exact ⟨c,⟨hcn,hcL,hdi ▸ hdL⟩,hc⟩

theorem torus_holomorphic_inverse_lifts_finite (L : PeriodPair) :
    {f : ℂ → ℂ | Differentiable ℂ f ∧ HasLatticeIncrements L f ∧ f 0 = 0 ∧
      ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ HasLatticeIncrements L g ∧
        g 0 = 0 ∧ Function.LeftInverse g f}.Finite := by
  apply ((period_lattice_automultipliers_finite L).image (fun c z : ℂ => c*z)).subset
  rintro f ⟨hf,hfi,hf0,g,hg,hgi,hg0,hinv⟩
  obtain ⟨c,hc,he⟩ := torus_holomorphic_inverse_lifts_linear L hf hg hfi hgi hf0 hg0 hinv
  exact ⟨c,hc,(funext he).symm⟩

theorem continuous_family_of_torus_lifts_constant (L : PeriodPair)
    {S : Type*} [TopologicalSpace S] [PreconnectedSpace S]
    {F : S → ℂ → ℂ} (hF : Continuous F)
    (hAut : ∀ s, Differentiable ℂ (F s) ∧ HasLatticeIncrements L (F s) ∧ F s 0 = 0 ∧
      ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ HasLatticeIncrements L g ∧
        g 0 = 0 ∧ Function.LeftInverse g (F s)) (s t : S) : F s = F t := by
  have hfinite : (range F).Finite := (torus_holomorphic_inverse_lifts_finite L).subset
    (by rintro _ ⟨s,rfl⟩; exact hAut s)
  have hconn : IsPreconnected (range F) := isPreconnected_range hF
  exact (hconn.isDiscrete_iff_subsingleton.mp hfinite.isDiscrete) ⟨s,rfl⟩ ⟨t,rfl⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.torus_holomorphic_inverse_lifts_finite
