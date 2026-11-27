import TwoAxisHelicoid.DiskCyclicQuotientParameter
import TwoAxisHelicoid.AnalyticRoundQuotient
import TwoAxisHelicoid.GenusOneUniformizationReduction

namespace TwoAxisHelicoid
open Complex Set Function TopologicalSpace Filter
open scoped Topology ContDiff Manifold

/-- The deck generator and its equivariance are constructed directly
from a topological marking of the cyclic covering fibers. -/
theorem marked_cyclic_deck_generator {P M : Type*} [TopologicalSpace P] (e : ℂ ≃ₜ P) {t : ℂ} (ht : t≠0)
    (p : P → M) (fib : ∀ x y, p x=p y ↔ ∃ n : ℤ, e.symm x=e.symm y+(n:ℂ)*t) :
    ∃ f : P ≃ₜ P, (∀ z, f z≠z) ∧ (∀ z, e (z+t)=f (e z)) ∧
      (∀ x, p (f x)=p x) ∧ ∀ x, p (f.symm x)=p x := by
  let f := (e.symm.trans (Homeomorph.addRight t)).trans e
  have eq (x : P) : f x=e (e.symm x+t) := rfl
  have lifts (x : P) : p (f x)=p x := (fib _ _).mpr ⟨1,by rw [eq,e.symm_apply_apply]; simp⟩
  refine ⟨f,?_,fun z => by rw [eq,e.symm_apply_apply],lifts,fun x => ?_⟩
  · intro z hz
    have bad := congrArg e.symm hz
    rw [eq,e.symm_apply_apply] at bad
    exact ht (add_eq_left.mp bad)
  · simpa only [f.apply_symm_apply] using (lifts (f.symm x)).symm

private def complex_univ_diffeomorph : Diffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) (⊤ : Opens ℂ) ℂ ω where
  toFun := Subtype.val
  invFun := fun z => ⟨z,Set.mem_univ _⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  contMDiff_toFun := contMDiff_subtype_val
  contMDiff_invFun := by
    intro z
    rw [← contMDiffWithinAt_univ]
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff _ _ _).mp contMDiffWithinAt_id

theorem cyclic_holomorphic_plane_quotient {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {t : ℂ} (ht : t≠0) (e : ℂ ≃ₜ ℂ) {p : ℂ → M}
    (cover : IsCoveringMap p) (onto : Surjective p) (localD : IsLocalDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω p)
    (fib : ∀ x y, p x=p y ↔ ∃ n : ℤ, e.symm x=e.symm y+(n:ℂ)*t) :
    ∃ T : Opens ℂ, IsRoundCylinderTarget T ∧ Nonempty (Diffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) M T ω) := by
  obtain ⟨f,free,step,act,_⟩ := marked_cyclic_deck_generator e ht p fib
  have translations := (holomorphic_plane_cover_of_localDiffeomorph cover onto localD).deck_translation f (funext act)
  have c : f 0≠0 := free 0
  obtain ⟨F,reg,im,per⟩ := plane_translation_quotient_parameter c
  let T : Opens ℂ := ⟨{z : ℂ | 0<‖z‖},isOpen_lt continuous_const continuous_norm⟩
  let S := (⊤ : Opens ℂ)
  let U := complex_univ_diffeomorph
  have diff : IsLocalDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (p ∘ U) := fun z =>
    IsLocalDiffeomorphAt.comp (K := 𝓘(ℂ,ℂ)) (P := M) (U.isLocalDiffeomorph z) (localD (U z))
  have same (x y : S) : F x.1=F y.1 ↔ p (U x)=p (U y) := by
    rw [fib]
    exact cyclic_coordinate_same_fibers e.toEquiv ht id injective_id
      (fun z => (step z).trans (translations _)) F per x.1 y.1
  obtain ⟨V,_⟩ := analytic_function_uniformizes_quotient S T diff (onto.comp U.surjective) F (fun z _ => reg z) im same
  exact ⟨T,Or.inl rfl,⟨V⟩⟩

theorem cyclic_holomorphic_disk_quotient {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    {t : ℂ} (ht : t≠0) (e : ℂ ≃ₜ RiemannUnitDisk) {p : RiemannUnitDisk → M}
    (onto : Surjective p) (localD : IsLocalDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω p)
    (fib : ∀ x y, p x=p y ↔ ∃ n : ℤ, e.symm x=e.symm y+(n:ℂ)*t) :
    ∃ T : Opens ℂ, IsRoundCylinderTarget T ∧ Nonempty (Diffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) M T ω) := by
  obtain ⟨f,free,step,act,back⟩ := marked_cyclic_deck_generator e ht p fib
  obtain ⟨F,T,shape,im,reg,same⟩ := disk_cyclic_quotient_parameter ht e.toEquiv f
    (holomorphic_of_cover_deck localD f.continuous act) (holomorphic_of_cover_deck localD f.symm.continuous back) free step
  let O : Opens ℂ := ⟨T,shape.isOpen⟩
  obtain ⟨U,_⟩ := analytic_function_uniformizes_quotient unitDiskOpen O localD onto F reg im
    (fun x y => (same x y).trans (fib x y).symm)
  exact ⟨O,shape,⟨U⟩⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.cyclic_holomorphic_disk_quotient
