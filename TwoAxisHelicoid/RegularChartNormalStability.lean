import TwoAxisHelicoid.CoreSheetPlaneConvergence
import TwoAxisHelicoid.EuclideanUnitChartNormal

namespace TwoAxisHelicoid
open Set Filter Metric Topology Submodule
open scoped Topology RealInnerProductSpace

/-- A regular surface differential in three dimensions admits exactly
two choices of unit normal. -/
theorem regular_plane_unit_normal_choices {T : ℂ →L[ℝ] SurfaceEuclideanSpace}
    (inj : Function.Injective T) {N m : SurfaceEuclideanSpace} (un : ‖N‖=1) (um : ‖m‖=1)
    (pn : ∀ v, ⟪T v,N⟫=0) (pm : ∀ v, ⟪T v,m⟫=0) : m=N ∨ m= -N := by
  have nn : N≠0 := fun eq => by simp [eq] at un
  have inc : T.toLinearMap.range ≤ (ℝ ∙ N)ᗮ := by
    rintro _ ⟨v,rfl⟩
    exact mem_orthogonal_singleton_iff_inner_left.mpr (pn v)
  let _ : Fact (Module.finrank ℝ SurfaceEuclideanSpace=2+1) := ⟨finrank_euclideanSpace_fin⟩
  have eq := Submodule.eq_of_le_of_finrank_eq inc
    (((LinearMap.finrank_range_of_inj (f := T.toLinearMap) inj).trans Complex.finrank_real_complex).trans
      (Submodule.finrank_orthogonal_span_singleton (n := 2) nn).symm)
  have perp : m∈T.toLinearMap.rangeᗮ := by
    apply (Submodule.mem_orthogonal _ _).mpr
    rintro _ ⟨v,rfl⟩
    exact pm v
  rw [eq,Submodule.orthogonal_orthogonal,Submodule.mem_span_singleton] at perp
  obtain ⟨a,ha⟩ := perp
  rw [← ha,norm_smul,un,mul_one,Real.norm_eq_abs] at um
  rcases le_or_gt 0 a with pos|neg
  · rw [abs_of_nonneg pos] at um
    exact Or.inl (by simpa only [um,one_smul] using ha.symm)
  · rw [abs_of_neg neg] at um
    have val : a= -1 := by linarith
    exact Or.inr (by simpa only [val,neg_one_smul] using ha.symm)

/-- An operator-norm neighborhood of a regular chart differential
controls both choices of unit normal simultaneously, for all charts
with differential in that neighborhood. -/
theorem nearby_regular_chart_normals {T : ℂ →L[ℝ] SurfaceEuclideanSpace}
    (inj : Function.Injective T) {N : SurfaceEuclideanSpace} (un : ‖N‖=1)
    (pn : ∀ v, ⟪T v,N⟫=0) {ε : ℝ} (pos : 0<ε) :
    ∀ᶠ A in 𝓝 T, ∀ m : SurfaceEuclideanSpace, ‖m‖=1 →
      (∀ v, ⟪A v,m⟫=0) → coreNormalDistance m N<ε := by
  let S := sphere (0:SurfaceEuclideanSpace) 1
  let _ : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  let P := (ℂ →L[ℝ] SurfaceEuclideanSpace) × S
  let D : Set P := {p | (∀ v, ⟪p.1 v,(p.2:SurfaceEuclideanSpace)⟫=0) ∧ ε≤coreNormalDistance p.2 N}
  have cm : Continuous (fun p : P => (p.2:SurfaceEuclideanSpace)) := continuous_subtype_val.comp continuous_snd
  have plane (v : ℂ) : IsClosed {p : P | ⟪p.1 v,(p.2:SurfaceEuclideanSpace)⟫=0} :=
    isClosed_eq ((continuous_fst.clm_apply continuous_const).inner cm) continuous_const
  have gap : Continuous (fun p : P => coreNormalDistance p.2 N) :=
    (cm.sub continuous_const).norm.min (cm.add continuous_const).norm
  have all : IsClosed {p : P | ∀ v, ⟪p.1 v,(p.2:SurfaceEuclideanSpace)⟫=0} := by
    simpa only [← ofPred_forall] using isClosed_iInter plane
  have closed : IsClosed D := all.inter (isClosed_le continuous_const gap)
  have imageClosed := isClosedMap_fst_of_compactSpace D closed
  have outside : T∉Prod.fst '' D := by
    rintro ⟨⟨A,m⟩,bad,rfl⟩
    have one : ‖(m:SurfaceEuclideanSpace)‖=1 := by simpa only [S,mem_sphere,dist_zero_right] using m.property
    rcases regular_plane_unit_normal_choices inj un one pn bad.1 with h|h
    · exact pos.not_ge (bad.2.trans ((min_le_left _ _).trans_eq (by rw [h,sub_self,norm_zero])))
    · exact pos.not_ge (bad.2.trans ((min_le_right _ _).trans_eq (by rw [h,neg_add_cancel,norm_zero])))
  filter_upwards [imageClosed.isOpen_compl.mem_nhds outside] with A ha
  intro m hm orth
  by_contra! large
  let s : S := ⟨m,by simpa only [S,mem_sphere,dist_zero_right] using hm⟩
  exact ha ⟨(A,s),⟨orth,large⟩,rfl⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.regular_plane_unit_normal_choices
#print axioms TwoAxisHelicoid.nearby_regular_chart_normals
