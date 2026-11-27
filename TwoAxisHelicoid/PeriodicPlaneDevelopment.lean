import TwoAxisHelicoid.TorusHolomorphicLifts
import TwoAxisHelicoid.ProperLocalCover
import TwoAxisHelicoid.BoundedDisplacementProper
import TwoAxisHelicoid.PlaneTranslationLattice
import Mathlib.Analysis.Normed.Operator.Banach

namespace TwoAxisHelicoid
open Complex Filter Set Function Topology
open scoped Topology Matrix

/-- A local plane coordinate on the topological universal cover, whose
increments under the two period generators are constant, is a global
homeomorphism. Openness rules out collinear increments. The residual
after subtracting their real-linear interpolation descends to the
compact torus and is bounded. -/
theorem periodic_local_development_is_homeomorph (L : PeriodPair) {D : ℂ → ℂ}
    (loc : IsLocalHomeomorph D) (b : Fin 2 → ℂ)
    (shift : ∀ (i : Fin 2) z, D (z+L.basis i)=D z+b i) :
    ∃ Φ : ℂ ≃ₜ ℂ, (Φ : ℂ → ℂ)=D := by
  let A := L.basis.constr ℝ b
  let residual := fun z => D z-A z
  have gen (i : Fin 2) : Periodic residual (L.basis i) := by
    intro z
    change D (z+L.basis i)-A (z+L.basis i)=D z-A z
    rw [shift,map_add,show A (L.basis i)=b i from L.basis.constr_basis ℝ b i]
    abel
  have per (z ω : ℂ) (h : ω∈L.lattice) : residual (z+ω)=residual z := by
    obtain ⟨m,n,rfl⟩ := PeriodPair.mem_lattice.mp h
    simpa only [PeriodPair.basis_zero,PeriodPair.basis_one,zsmul_eq_mul] using! (((gen 0).zsmul m).add_period ((gen 1).zsmul n)) z
  have compact := IsZLattice.isCompact_range_of_periodic L.lattice residual
    (loc.continuous.sub A.continuous_of_finiteDimensional) per
  have onto : Surjective A := by
    by_contra h
    have n : LinearMap.range A≠⊤ := fun eq => h (LinearMap.range_eq_top.mp eq)
    obtain ⟨f,hf,ker⟩ := (LinearMap.range A).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr n)
    let g := f.toContinuousLinearMap
    have eq (z : ℂ) : g (residual z)=g (D z) := by
      change f (D z-A z)=f (D z)
      rw [map_sub,show f (A z)=0 from ker ⟨z,rfl⟩,sub_zero]
    have r : range (g ∘ D)=g '' range residual := by
      rw [← range_comp]
      exact congrArg range (funext fun z => (eq z).symm)
    have kc : IsCompact (range (g ∘ D)) := r ▸ compact.image g.continuous
    have go : IsOpenMap g := g.isOpenMap (LinearMap.surjective hf)
    have oc : IsClopen (range (g ∘ D)) := ⟨kc.isClosed,(go.comp loc.isOpenMap).isOpen_range⟩
    exact noncompact_univ ℝ ((oc.eq_univ (range_nonempty _)) ▸ kc)
  let E := (LinearEquiv.ofBijective A ⟨LinearMap.injective_iff_surjective.mpr onto,onto⟩).toContinuousLinearEquiv
  obtain ⟨B,bound⟩ := compact.isBounded.exists_norm_le
  have proper : IsProperMap (D ∘ E.symm) := by
    apply bounded_displacement_isProperMap (loc.continuous.comp E.symm.continuous)
    intro x
    have h := bound (residual (E.symm x)) (mem_range_self _)
    change ‖D (E.symm x)-E (E.symm x)‖≤B at h
    rw [E.apply_symm_apply,norm_sub_rev] at h
    exact h
  have hD : IsProperMap D := by
    have h := proper.comp E.toHomeomorph.isProperMap
    have eq : (D ∘ E.symm) ∘ E.toHomeomorph=D := funext fun z => congrArg D (E.symm_apply_apply z)
    exact eq ▸ h
  have cov := proper_local_homeomorph_isCoveringMap hD loc
  obtain ⟨g,⟨g0,right⟩,_⟩ := cov.existsUnique_continuousMap_lifts (ContinuousMap.id ℂ) (D 0) 0 rfl
  have left : g ∘ D=id := cov.eq_of_comp_eq (g.continuous.comp loc.continuous) continuous_id
    (funext fun x => congrFun right (D x)) 0 g0
  exact ⟨⟨⟨D,g,congrFun left,congrFun right⟩,loc.continuous,g.continuous⟩,rfl⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.periodic_local_development_is_homeomorph
