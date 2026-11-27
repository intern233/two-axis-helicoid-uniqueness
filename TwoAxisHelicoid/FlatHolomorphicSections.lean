import TwoAxisHelicoid.RhombicLattice
import Mathlib.Analysis.Complex.Liouville
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace TwoAxisHelicoid
open Complex Set

/-- Holomorphic sections of the flat line bundle with constant multipliers
`ε₁, ε₂`, represented by their entire equivariant functions on the cover. -/
noncomputable def flatHolomorphicSections (t : ℝ) (ε₁ ε₂ : ℂ) : Submodule ℂ (ℂ → ℂ) where
  carrier := {f | Differentiable ℂ f ∧
    (∀ z, f (z+2) = ε₁*f z) ∧ (∀ z, f (z+(1+I*t)) = ε₂*f z)}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    refine ⟨hf.1.add hg.1,?_,?_⟩
    · intro z
      simp only [Pi.add_apply,hf.2.1,hg.2.1]
      ring
    · intro z
      simp only [Pi.add_apply,hf.2.2,hg.2.2]
      ring
  smul_mem' := by
    intro c f hf
    refine ⟨hf.1.const_smul c,?_,?_⟩
    · intro z
      simp only [Pi.smul_apply,smul_eq_mul,hf.2.1]
      ring
    · intro z
      simp only [Pi.smul_apply,smul_eq_mul,hf.2.2]
      ring

theorem flatHolomorphicSections_constant {t : ℝ} (ht : 0 < t) {ε₁ ε₂ : ℂ}
    (hε₁ : ‖ε₁‖ = 1) (hε₂ : ‖ε₂‖ = 1) {f : ℂ → ℂ}
    (hf : f ∈ flatHolomorphicSections t ε₁ ε₂) (z w : ℂ) : f z = f w := by
  have h1 : Function.Periodic (fun z => ‖f z‖) 2 := by
    intro z
    change ‖f (z+2)‖ = ‖f z‖
    rw [hf.2.1,norm_mul,hε₁,one_mul]
  have h2 : Function.Periodic (fun z => ‖f z‖) (1+I*t) := by
    intro z
    change ‖f (z+(1+I*t))‖ = ‖f z‖
    rw [hf.2.2,norm_mul,hε₂,one_mul]
  have hL : ∀ z u, u ∈ (rhombicPeriodPair t ht).lattice → ‖f (z+u)‖ = ‖f z‖ := by
    intro z u hu
    obtain ⟨m,n,he⟩ := PeriodPair.mem_lattice.mp hu
    rw [← he]
    change ‖f (z+((m : ℂ)*2+(n : ℂ)*(1+I*t)))‖ = _
    have h1' := h1.zsmul m z
    have h2' := h2.zsmul n (z+(m : ℂ)*2)
    simp only [zsmul_eq_mul] at h1' h2'
    rw [← add_assoc,h2',h1']
  have hb := (IsZLattice.isCompact_range_of_periodic (rhombicPeriodPair t ht).lattice
    (fun z => ‖f z‖) hf.1.continuous.norm hL).isBounded
  obtain ⟨C,hC⟩ := isBounded_iff_forall_norm_le.mp hb
  have hfB : Bornology.IsBounded (range f) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨C,?_⟩
    rintro _ ⟨v,rfl⟩
    simpa only [norm_norm] using hC ‖f v‖ ⟨v,rfl⟩
  exact hf.1.apply_eq_apply_of_bounded hfB z w

theorem flatHolomorphicSections_zero_of_nontrivial {t : ℝ} (ht : 0 < t) {ε₁ ε₂ : ℂ}
    (hε₁ : ‖ε₁‖ = 1) (hε₂ : ‖ε₂‖ = 1) (hne : ε₁ ≠ 1 ∨ ε₂ ≠ 1) {f : ℂ → ℂ}
    (hf : f ∈ flatHolomorphicSections t ε₁ ε₂) : f = 0 := by
  have hc := flatHolomorphicSections_constant ht hε₁ hε₂ hf
  have h0 : f 0 = 0 := by
    rcases hne with hne | hne
    · have h := hf.2.1 0
      rw [hc (0+2) 0] at h
      have he : (ε₁-1)*f 0 = 0 := by linear_combination -h
      exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hne)
    · have h := hf.2.2 0
      rw [hc (0+(1+I*t)) 0] at h
      have he : (ε₂-1)*f 0 = 0 := by linear_combination -h
      exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hne)
  funext z
  exact (hc z 0).trans h0

noncomputable def trivialFlatSectionsEquiv (t : ℝ) (ht : 0 < t) :
    flatHolomorphicSections t 1 1 ≃ₗ[ℂ] ℂ where
  toFun := fun f => f.val 0
  invFun := fun c => ⟨fun _ => c,differentiable_const c,by simp,by simp⟩
  left_inv := by
    intro f
    apply Subtype.ext
    funext z
    exact (flatHolomorphicSections_constant ht (by norm_num) (by norm_num) f.property z 0).symm
  right_inv := by intro c; rfl
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem trivialFlatSections_finrank {t : ℝ} (ht : 0 < t) :
    Module.finrank ℂ (flatHolomorphicSections t 1 1) = 1 := by
  rw [(trivialFlatSectionsEquiv t ht).finrank_eq]
  exact Module.finrank_self ℂ

theorem nontrivialFlatSections_finrank {t : ℝ} (ht : 0 < t) {ε₁ ε₂ : ℂ}
    (hε₁ : ‖ε₁‖ = 1) (hε₂ : ‖ε₂‖ = 1) (hne : ε₁ ≠ 1 ∨ ε₂ ≠ 1) :
    Module.finrank ℂ (flatHolomorphicSections t ε₁ ε₂) = 0 := by
  have he : flatHolomorphicSections t ε₁ ε₂ = ⊥ := by
    apply le_antisymm _ bot_le
    intro f hf
    exact (flatHolomorphicSections_zero_of_nontrivial ht hε₁ hε₂ hne hf) ▸ Submodule.zero_mem _
  rw [he]
  simp

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.trivialFlatSections_finrank
#print axioms TwoAxisHelicoid.nontrivialFlatSections_finrank
