import TwoAxisHelicoid.AbelianIntegralDevelopment
import TwoAxisHelicoid.NoncollinearHolomorphicPeriods

namespace TwoAxisHelicoid.HolomorphicCoefficientDisks
open Complex Set Filter Topology Function
open scoped Topology ContDiff Manifold

/-- For a nonzero holomorphic differential on a compact topological
torus, its actual polygonal periods form a full lattice. Its integral
on the topological universal cover is proper and stays a bounded
distance from a real-linear isomorphism even if zeros are allowed. -/
theorem abelian_integral_full_period_lattice {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] [CompactSpace M] {L : PeriodPair} (mark : M ≃ₜ PeriodTorus L)
    (A : HolomorphicCoefficientDisks M) (compat : A.compatibleOneForm) {x : M} (nonzero : A.coefficient x (chartAt ℂ x x)≠0) :
    let p := mark.symm ∘ periodTorusProjection L
    ∃ (D : ℂ → ℂ) (E : ℂ ≃L[ℝ] ℂ) (B : ℝ), A.IsAbelianIntegral p D ∧ IsProperMap D ∧
      (∀ z, ‖D z-E z‖≤B) ∧ (∀ z period, period∈L.lattice → D (z+period)=D z+E period) ∧
      ∀ r : ℂ, Nonempty (A.IntegralChain (p 0) (p 0) r) ↔ ∃ period∈L.lattice, E period=r := by
  let p := mark.symm ∘ periodTorusProjection L
  have cover : IsCoveringMap p := (periodTorusProjection_isCoveringMap L).homeomorph_comp mark.symm
  have sur : Surjective p := mark.symm.surjective.comp (Quotient.mk_surjective : Surjective (periodTorusProjection L))
  let _ : PreconnectedSpace M := (sur.connectedSpace cover.continuous).toPreconnectedSpace
  obtain ⟨D,dc,dev⟩ := A.exists_abelian_integral compat p cover.continuous
  have fix (z period : ℂ) (member : period∈L.lattice) : p (z+period)=p z := by
    apply congrArg mark.symm
    apply (periodTorusProjection_eq_iff L _ _).mpr
    rw [show z-(z+period)= -period by abel]
    exact L.lattice.neg_mem member
  let b := fun i : Fin 2 => D (L.basis i)-D 0
  let T := L.basis.constr ℝ b
  let residual := fun z => D z-T z
  have gen (i : Fin 2) : Periodic residual (L.basis i) := by
    have mem : L.basis i∈L.lattice := by fin_cases i <;> simp [L.ω₁_mem_lattice,L.ω₂_mem_lattice]
    intro z
    change D (z+L.basis i)-T (z+L.basis i)=D z-T z
    rw [abelian_integral_period_is_constant dev (fun z => fix z _ mem),map_add]
    rw [show T (L.basis i)=b i from L.basis.constr_basis ℝ b i]
    dsimp only [b]
    abel
  have per (z period : ℂ) (hw : period∈L.lattice) : residual (z+period)=residual z := by
    obtain ⟨m,n,rfl⟩ := PeriodPair.mem_lattice.mp hw
    simpa only [PeriodPair.basis_zero,PeriodPair.basis_one,zsmul_eq_mul] using! (((gen 0).zsmul m).add_period ((gen 1).zsmul n)) z
  have addD (z period : ℂ) (hw : period∈L.lattice) : D (z+period)=D z+T period := by
    have h := per z period hw
    change D (z+period)-T (z+period)=D z-T z at h
    rw [map_add] at h
    linear_combination h
  have spans (r : ℂ) : Nonempty (A.IntegralChain (p 0) (p 0) r) ↔ ∃ v∈L.lattice, T v=r := by
    constructor
    · rintro ⟨c⟩
      obtain ⟨v,hv,e⟩ := integral_chain_lifts_increment cover dev c 0 rfl
      have eq := mark.symm.injective hv
      have lv : v∈L.lattice := by simpa only [sub_zero] using (periodTorusProjection_eq_iff L 0 v).mp eq.symm
      have h := addD 0 v lv
      rw [zero_add] at h
      exact ⟨v,lv,by linear_combination e-h⟩
    · rintro ⟨v,lv,rfl⟩
      have e := abelian_increment_has_integral_chain cover.continuous dev 0 v
      have a := addD 0 v lv
      have q := fix 0 v lv
      rw [zero_add] at a q
      rwa [q,a,add_sub_cancel_left] at e
  obtain ⟨v,w,pv,pw,det⟩ := exists_two_independent_holomorphic_periods A (p 0) x nonzero
  obtain ⟨v',_,hv⟩ := (spans v).mp pv
  obtain ⟨w',_,hw⟩ := (spans w).mp pw
  have onto : Surjective T := by
    intro z
    let k := v.re*w.im-v.im*w.re
    have hk : k≠0 := det
    refine ⟨((z.re*w.im-z.im*w.re)/k) • v' + ((v.re*z.im-v.im*z.re)/k) • w',?_⟩
    rw [map_add,map_smul,map_smul,hv,hw]
    apply Complex.ext
    · simp only [Complex.add_re,Complex.smul_re,smul_eq_mul]
      calc
        _ = ((z.re*w.im-z.im*w.re)*v.re+(v.re*z.im-v.im*z.re)*w.re)/k := by ring
        _ = z.re := (div_eq_iff hk).mpr (by dsimp only [k]; ring)
    · simp only [Complex.add_im,Complex.smul_im,smul_eq_mul]
      calc
        _ = ((z.re*w.im-z.im*w.re)*v.im+(v.re*z.im-v.im*z.re)*w.im)/k := by ring
        _ = z.im := (div_eq_iff hk).mpr (by dsimp only [k]; ring)
  let E := (LinearEquiv.ofBijective T ⟨LinearMap.injective_iff_surjective.mpr onto,onto⟩).toContinuousLinearEquiv
  have compact := IsZLattice.isCompact_range_of_periodic L.lattice residual (dc.sub T.continuous_of_finiteDimensional) per
  obtain ⟨B,bound⟩ := compact.isBounded.exists_norm_le
  have val (z : ℂ) : ‖D z-E z‖≤B := bound _ (mem_range_self z)
  have prop : IsProperMap (D ∘ E.symm) := by
    apply bounded_displacement_isProperMap (dc.comp E.symm.continuous) (B := B)
    intro z
    change ‖z-D (E.symm z)‖≤B
    rw [norm_sub_rev]
    simpa only [E.apply_symm_apply] using val (E.symm z)
  have propD := prop.comp E.toHomeomorph.isProperMap
  have cancel : (D ∘ E.symm) ∘ E.toHomeomorph=D := funext fun z => congrArg D (E.symm_apply_apply z)
  exact ⟨D,E,B,dev,cancel ▸ propD,val,addD,spans⟩

end TwoAxisHelicoid.HolomorphicCoefficientDisks
#print axioms TwoAxisHelicoid.HolomorphicCoefficientDisks.abelian_integral_full_period_lattice
