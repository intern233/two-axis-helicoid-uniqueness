import TwoAxisHelicoid.RegionBoundaryPatches
import TwoAxisHelicoid.CompactCurveChartPartition

namespace TwoAxisHelicoid
open Complex Set Filter Topology Function
open scoped Topology ContDiff Manifold

/-- The local graph description of a smooth boundary, in a positively
oriented conformal coordinate, on the actual physical surface. -/
def HasSmoothCurveBoundary {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] (Ω : Set M) : Prop :=
  ∀ x∈frontier Ω, ∃ e : OpenPartialHomeomorph M ℂ, e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M ∧
    ∃ G : CurveBoundaryGraph e Ω, (CurveRegionPatch.boundary G).carrier∈𝓝 x

/-- A finite smooth partition for the closure of an arbitrary
relatively compact region. Each cutoff is supported compactly inside
one interior chart or one oriented boundary graph. -/
structure CurveRegionPartition {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] (Ω : Set M) where
  indices : Finset (closure Ω)
  chart : indices → OpenPartialHomeomorph M ℂ
  member : ∀ i, chart i∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M
  patch : (i : indices) → CurveRegionPatch (chart i) Ω
  weight : indices → M → ℝ
  unity : ∀ x∈closure Ω, ∑ i, weight i x=1
  nonnegative : ∀ i x, 0≤weight i x
  smooth : ∀ i, ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ) ∞ (weight i)
  compact : ∀ i, IsCompact (tsupport (weight i))
  supported : ∀ i, tsupport (weight i)⊆(patch i).carrier

theorem exists_curve_region_partition {M : Type*} [TopologicalSpace M] [T2Space M] [SigmaCompactSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {Ω : Set M} (op : IsOpen Ω)
    (compact : IsCompact (closure Ω)) (boundary : HasSmoothCurveBoundary Ω) :
    Nonempty (CurveRegionPartition Ω) := by
  classical
  let _ := complex_curve_underlying_real_manifold M
  let _ := ChartedSpace.locallyCompactSpace ℂ M
  have localData (x : closure Ω) :
      ∃ e : OpenPartialHomeomorph M ℂ, e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M ∧
        ∃ P : CurveRegionPatch e Ω, P.carrier∈𝓝 (x:M) := by
    by_cases h : (x:M)∈Ω
    · let e := chartAt ℂ (x:M)
      exact ⟨e,IsManifold.chart_mem_maximalAtlas _,.interior,
        inter_mem (e.open_source.mem_nhds (mem_chart_source ℂ (x:M))) (op.mem_nhds h)⟩
    · have fr : (x:M)∈frontier Ω := by simpa only [frontier,op.interior_eq] using (show (x:M)∈closure Ω \ Ω from ⟨x.2,h⟩)
      obtain ⟨e,he,G,nh⟩ := boundary _ fr
      exact ⟨e,he,.boundary G,nh⟩
  choose e he P nh using localData
  have shrinks (x : closure Ω) : ∃ K, IsCompact K ∧ (x:M)∈interior K ∧ K⊆(P x).carrier := by
    obtain ⟨U,sub,oU,xU⟩ := mem_nhds_iff.mp (nh x)
    obtain ⟨K,ck,inner,small⟩ := exists_compact_between (isCompact_singleton (x:=(x:M))) oU (singleton_subset_iff.mpr xU)
    exact ⟨K,ck,inner (mem_singleton _),small.trans sub⟩
  choose K ck inner small using shrinks
  obtain ⟨C,cover⟩ := compact.elim_finite_subcover (fun x => interior (K x)) (fun _ => isOpen_interior)
    (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,inner _⟩)
  have cv : closure Ω⊆⋃ i : C, interior (K i.1) := by
    intro x hx
    obtain ⟨i,hi,mem⟩ := mem_iUnion₂.mp (cover hx)
    exact mem_iUnion.mpr ⟨⟨i,hi⟩,mem⟩
  obtain ⟨ρ,sub⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ,ℂ) isClosed_closure
    (fun i : C => interior (K i.1)) (fun _ => isOpen_interior) cv
  refine ⟨⟨C,fun i => e i.1,fun i => he i.1,fun i => P i.1,fun i => ρ i,?_,ρ.nonneg,
    fun i => (ρ i).contMDiff,?_,?_⟩⟩
  · intro x hx
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
  · exact fun i => (ck i.1).of_isClosed_subset (isClosed_tsupport _) ((sub i).trans interior_subset)
  · exact fun i => ((sub i).trans interior_subset).trans (small i.1)

/-- Real smooth cutoffs in a holomorphic chart are ordinary C¹
complex-valued functions of the coordinate. The chart here can be
any member of the maximal analytic atlas. -/
theorem real_cutoff_in_complex_chart {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] (ρ : M → ℝ) (smooth : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ) ∞ ρ)
    {e : OpenPartialHomeomorph M ℂ} (he : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
    {z : ℂ} (hz : z∈e.target) : ContDiffAt ℝ 1 (fun w => (ρ (e.symm w):ℂ)) z := by
  let _ := complex_curve_underlying_real_manifold M
  let c := chartAt ℂ (e.symm z)
  let t := e.symm.trans c
  have hit : z∈t.source := ⟨hz,mem_chart_source ℂ _⟩
  have hol := complexAtlas_realized_transition he (IsManifold.chart_mem_maximalAtlas _) hit
  have der : ContDiffAt ℝ 1 t z := (hol.restrict_scalars ℝ).of_le (by simp)
  have inv : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ c.symm (t z) :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas _) (c.map_source hit.2)
  have d := ((smooth.contMDiffAt.comp (t z) inv).contDiffAt.of_le (show (1:WithTop ℕ∞)≤∞ by simp)).comp z der
  apply (Complex.ofRealCLM.contDiff.contDiffAt.comp z d).congr_of_eventuallyEq
  filter_upwards [t.open_source.mem_nhds hit] with w hw
  change (ρ (e.symm w):ℂ)=(ρ (c.symm (c (e.symm w))):ℂ)
  rw [c.left_inv (show e.symm w∈c.source from hw.2)]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.exists_curve_region_partition
#print axioms TwoAxisHelicoid.real_cutoff_in_complex_chart

