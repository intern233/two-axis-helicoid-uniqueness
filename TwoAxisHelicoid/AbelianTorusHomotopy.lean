import TwoAxisHelicoid.TorusAbelianPeriodLattice

namespace TwoAxisHelicoid.HolomorphicCoefficientDisks
open Complex Set Function Topology
open scoped Topology ContDiff Manifold unitInterval

/-- A proper abelian integral of a nonzero differential descends on the
torus. After identifying its period lattice by the real-linear map, the
descended map is homotopic to the original topological marking. -/
theorem abelian_period_map_homotopic_to_marking {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] [CompactSpace M] {L : PeriodPair} (mark : M ≃ₜ PeriodTorus L)
    (A : HolomorphicCoefficientDisks M) (compat : A.compatibleOneForm) {x : M} (nonzero : A.coefficient x (chartAt ℂ x x)≠0) :
    let p := mark.symm ∘ periodTorusProjection L
    ∃ (D : ℂ → ℂ) (E : ℂ ≃L[ℝ] ℂ) (F : C(M,PeriodTorus L)), A.IsAbelianIntegral p D ∧ IsProperMap D ∧
      (∀ z, F (p z)=periodTorusProjection L (E.symm (D z))) ∧
      (∀ z b, b∈L.lattice → D (z+b)=D z+E b) ∧ ContinuousMap.Homotopic (mark : C(M,PeriodTorus L)) F := by
  obtain ⟨D,E,_,dev,prop,_,inc,_⟩ := abelian_integral_full_period_lattice mark A compat nonzero
  let R := fun z : ℂ => E.symm (D z)-z
  have per (z period : ℂ) (h : period∈L.lattice) : R (z+period)=R z := by
    dsimp only [R]
    rw [inc z period h,map_add,E.symm_apply_apply]
    abel
  let f := periodTorusLift L R per
  have cont : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro q
    obtain ⟨z,rfl⟩ := (Quotient.mk_surjective : Surjective (periodTorusProjection L)) q
    exact periodTorusLift_continuousAt L R per (((E.symm.continuous.comp prop.continuous).sub continuous_id).continuousAt)
  let H : C(unitInterval × M,PeriodTorus L) := ⟨fun t => mark t.2+periodTorusProjection L ((t.1:ℝ) • f (mark t.2)),
    (mark.continuous.comp continuous_snd).add (QuotientAddGroup.continuous_mk.comp
      ((continuous_subtype_val.comp continuous_fst).smul (cont.comp (mark.continuous.comp continuous_snd))))⟩
  let F : C(M,PeriodTorus L) := H.comp ⟨fun y => (1,y),continuous_const.prodMk continuous_id⟩
  refine ⟨D,E,F,dev,prop,?_,inc,⟨⟨H,?_,fun _ => rfl⟩⟩⟩
  · intro z
    change mark (mark.symm _) + periodTorusProjection L (((1:unitInterval):ℝ) • f (mark (mark.symm _))) = _
    simp only [mark.apply_symm_apply,show ((1:unitInterval):ℝ)=1 from rfl,one_smul]
    change QuotientAddGroup.mk z + QuotientAddGroup.mk (E.symm (D z)-z) = _
    change QuotientAddGroup.mk (z+(E.symm (D z)-z)) = _
    rw [show z+(E.symm (D z)-z)=E.symm (D z) by abel]
    rfl
  · intro y
    change mark y+periodTorusProjection L (((0:unitInterval):ℝ) • f (mark y))=mark y
    simp [periodTorusProjection]

end TwoAxisHelicoid.HolomorphicCoefficientDisks
#print axioms TwoAxisHelicoid.HolomorphicCoefficientDisks.abelian_period_map_homotopic_to_marking
