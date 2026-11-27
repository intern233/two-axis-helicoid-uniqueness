import TwoAxisHelicoid.PointedTorusUniformization
import TwoAxisHelicoid.HolomorphicCurveRealSmooth

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff Manifold
set_option maxHeartbeats 1000000

/-- A continuous real-linear map of the covering planes descending through
the lattice quotients is smooth in the canonical torus charts. -/
theorem real_linear_torus_lift_smooth (L M : PeriodPair) (A : ℂ →L[ℝ] ℂ)
    (f : PeriodTorus L → PeriodTorus M)
    (lift : ∀ z, f (periodTorusProjection L z)=periodTorusProjection M (A z)) :
    ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ f := by
  intro q
  let e := chartAt ℂ q
  have he : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ e q := contMDiffAt_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ q)) (mem_chart_source ℂ q)
  have hA : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ A (e q) := contMDiffAt_iff_contDiffAt.mpr A.contDiff.contDiffAt
  apply ((holomorphic_curve_map_real_smooth (periodTorusProjection_contMDiff M)).contMDiffAt.comp q
    (hA.comp q he)).congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds (mem_chart_source ℂ q)] with x hx
  change f x=periodTorusProjection M (A (e x))
  rw [← lift]
  exact congrArg f (by rw [← periodTorus_chart_symm_eq_projection L q]; exact (e.left_inv hx).symm)

theorem real_map_period_span (L M : PeriodPair) (A : ℂ ≃L[ℝ] ℂ)
    (h₁ : A L.ω₁=M.ω₁) (h₂ : A L.ω₂=M.ω₂) {z : ℂ} (hz : z∈L.lattice) : A z∈M.lattice := by
  obtain ⟨m,n,rfl⟩ := PeriodPair.mem_lattice.mp hz
  apply PeriodPair.mem_lattice.mpr
  refine ⟨m,n,?_⟩
  simp only [← zsmul_eq_mul,map_add,map_zsmul,h₁,h₂]

/-- Every prescribed lattice marking of a flat torus gives a smooth
marking of another flat torus. The map sends the marked point and the
two ordered period generators to their prescribed counterparts. -/
theorem prescribed_punctured_period_torus_diffeomorphism (L M : PeriodPair) :
    ∃ (A : ℂ ≃L[ℝ] ℂ) (E : Diffeomorph 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) (PeriodTorus L) (PeriodTorus M) ∞)
      (e : Diffeomorph 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) (PuncturedPeriodTorus L) (PuncturedPeriodTorus M) ∞),
      A L.ω₁=M.ω₁ ∧ A L.ω₂=M.ω₂ ∧ E 0=0 ∧
      (∀ z, E (periodTorusProjection L z)=periodTorusProjection M (A z)) ∧ ∀ q, (e q).1=E q.1 := by
  let A := (L.basis.equiv M.basis (Equiv.refl (Fin 2))).toContinuousLinearEquiv
  have generators (i : Fin 2) : A (L.basis i)=M.basis i := by
    change L.basis.equiv M.basis (Equiv.refl (Fin 2)) (L.basis i)=M.basis i
    simp
  have h₁ : A L.ω₁=M.ω₁ := by simpa using generators 0
  have h₂ : A L.ω₂=M.ω₂ := by simpa using generators 1
  have fperiod (z w : ℂ) (hw : w∈L.lattice) :
      periodTorusProjection M (A (z+w))=periodTorusProjection M (A z) := by
    rw [map_add,periodTorusProjection_add_lattice M _ _ (real_map_period_span L M A h₁ h₂ hw)]
  have iperiod (z w : ℂ) (hw : w∈M.lattice) :
      periodTorusProjection L (A.symm (z+w))=periodTorusProjection L (A.symm z) := by
    rw [map_add,periodTorusProjection_add_lattice L _ _ (real_map_period_span M L A.symm
      (A.symm_apply_eq.mpr h₁.symm) (A.symm_apply_eq.mpr h₂.symm) hw)]
  let f := periodTorusLift L (fun z => periodTorusProjection M (A z)) fperiod
  let g := periodTorusLift M (fun z => periodTorusProjection L (A.symm z)) iperiod
  have sf := real_linear_torus_lift_smooth L M A.toContinuousLinearMap f (fun _ => rfl)
  have sg := real_linear_torus_lift_smooth M L A.symm.toContinuousLinearMap g (fun _ => rfl)
  let E : Diffeomorph 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) (PeriodTorus L) (PeriodTorus M) ∞ :=
    ⟨⟨f,g,fun q => by
        obtain ⟨z,rfl⟩ := Quotient.exists_rep q
        exact congrArg (periodTorusProjection L) (A.symm_apply_apply z),
      fun q => by
        obtain ⟨z,rfl⟩ := Quotient.exists_rep q
        exact congrArg (periodTorusProjection M) (A.apply_symm_apply z)⟩,sf,sg⟩
  have zero : E 0=0 := by change periodTorusProjection M (A 0)=0; rw [map_zero]; rfl
  let T := E.toHomeomorph
  let t := T.subtype (p:=fun q => q≠0) (q:=fun q => q≠0) (fun q => by
    change q≠0 ↔ E q≠0
    rw [← zero]
    exact ⟨fun h he => h (E.injective he), fun h he => h (congrArg (fun p => E p) he)⟩)
  have fwd : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ t := by
    intro q
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff (U:=puncturedPeriodTorusOpen M) t univ q).mp
    exact (sf.comp (contMDiff_subtype_val (U:=puncturedPeriodTorusOpen L))).contMDiffAt.contMDiffWithinAt
  have inv : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ t.symm := by
    intro q
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff (U:=puncturedPeriodTorusOpen L) t.symm univ q).mp
    exact (sg.comp (contMDiff_subtype_val (U:=puncturedPeriodTorusOpen M))).contMDiffAt.contMDiffWithinAt
  exact ⟨A,E,⟨t.toEquiv,fwd,inv⟩,h₁,h₂,zero,fun _ => rfl,fun _ => rfl⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.prescribed_punctured_period_torus_diffeomorphism

