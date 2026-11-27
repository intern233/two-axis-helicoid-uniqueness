module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Tactic.Ring

public section

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory Topology
open scoped ContDiff Manifold Topology

universe u

private theorem compact_cover_transition {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    {e d : OpenPartialHomeomorph M ℂ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) (hd : d ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
    {z : ℂ} (hz : z ∈ (e.symm.trans d).source) : ContDiffAt ℂ ω (e.symm.trans d) z := by
  have h : ContDiffOn ℂ ω (e.symm.trans d) (e.symm.trans d).source := by
    simpa only [mfld_simps] using! (𝓘(ℂ,ℂ)).contDiffOn_extendCoordChange he hd
  exact h.contDiffAt ((e.symm.trans d).open_source.mem_nhds hz)

private theorem compact_cover_jacobian {f : ℂ → ℂ} {z : ℂ} (h : DifferentiableAt ℂ f z) :
    (fderiv ℝ f z).det = ‖deriv f z‖^2 := by
  rw [(h.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv]
  change LinearMap.det ((ContinuousLinearMap.toSpanSingleton ℂ (deriv f z)).toLinearMap.restrictScalars ℝ)=_
  rw [LinearMap.det_restrictScalars]
  change Algebra.norm ℝ ((ContinuousLinearMap.toSpanSingleton ℂ (deriv f z)).det)=_
  rw [ContinuousLinearMap.det_toSpanSingleton,Algebra.norm_complex_eq]
  exact Complex.normSq_eq_norm_sq _

/-- A finite atlas partition of unity on a prescribed compact support.
Values outside the support are unrestricted. -/
structure CompactTestChartCover {M : Type u} [TopologicalSpace M] [ChartedSpace ℂ M] (K : Set M) where
  indices : Type u
  [finite : Fintype indices]
  chart : indices → OpenPartialHomeomorph M ℂ
  member : ∀ i, chart i∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M
  weight : indices → M → ℝ
  unity : ∀ p∈K, ∑ i, weight i p = 1
  smooth : ∀ i, ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ) ∞ (weight i)
  compact : ∀ i, IsCompact (tsupport (weight i))
  supported : ∀ i, tsupport (weight i) ⊆ (chart i).source

attribute [instance] CompactTestChartCover.finite

theorem exists_compact_test_chart_cover {M : Type u} [TopologicalSpace M] [T2Space M] [SigmaCompactSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {K : Set M} (compact : IsCompact K) :
    Nonempty (CompactTestChartCover K) := by
  classical
  let : IsManifold 𝓘(ℝ,ℂ) ∞ M := by
    apply isManifold_of_contDiffOn
    intro e d he hd z hz
    have h := compact_cover_transition (IsManifold.subset_maximalAtlas he)
      (IsManifold.subset_maximalAtlas hd) hz.1
    exact ((h.restrict_scalars ℝ).of_le (show (∞ : WithTop ℕ∞) ≤ ω by simp)).contDiffWithinAt
  let _ := ChartedSpace.locallyCompactSpace ℂ M
  have shrink (p : K) : ∃ L : Set M, IsCompact L ∧ (p:M) ∈ interior L ∧ L ⊆ (chartAt ℂ (p:M)).source := by
    obtain ⟨L,ck,inner,sub⟩ := exists_compact_between (isCompact_singleton (x := (p:M)))
      (chartAt ℂ (p:M)).open_source (singleton_subset_iff.mpr (mem_chart_source ℂ (p:M)))
    exact ⟨L,ck,inner (mem_singleton _),sub⟩
  choose L ck inner sub using shrink
  obtain ⟨C,all⟩ := compact.elim_finite_subcover (fun p : K => interior (L p)) (fun _ => isOpen_interior)
    (fun p hp => mem_iUnion.mpr ⟨⟨p,hp⟩,inner _⟩)
  have cover : K ⊆ ⋃ i : C, interior (L i.1) := by
    intro p hp
    obtain ⟨i,hi,mem⟩ := mem_iUnion₂.mp (all hp)
    exact mem_iUnion.mpr ⟨⟨i,hi⟩,mem⟩
  obtain ⟨ρ,small⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ,ℂ) compact.isClosed
    (fun i : C => interior (L i.1)) (fun _ => isOpen_interior) cover
  exact ⟨{ indices := C
           chart := fun i => chartAt ℂ (i.1.1:M)
           member := fun i => IsManifold.chart_mem_maximalAtlas _
           weight := fun i => ρ i
           unity := fun p hp => by simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hp
           smooth := fun i => (ρ i).contMDiff
           compact := fun i => (ck i.1).of_isClosed_subset (isClosed_tsupport _) ((small i).trans interior_subset)
           supported := fun i => ((small i).trans interior_subset).trans (sub i.1) }⟩

noncomputable def CompactTestChartCover.integral {M : Type u} [TopologicalSpace M] [ChartedSpace ℂ M]
    {K : Set M} (P : CompactTestChartCover K) (f : OpenPartialHomeomorph M ℂ → ℂ → ℝ) : ℝ :=
  ∑ i, ∫ z in (P.chart i).target, P.weight i ((P.chart i).symm z)*f (P.chart i) z

private theorem compact_test_swap {M : Type u} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    {e d : OpenPartialHomeomorph M ℂ} (he : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
    (hd : d∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) {ρ σ : M → ℝ}
    (se : tsupport ρ ⊆ e.source) (sd : tsupport σ ⊆ d.source) {f g : ℂ → ℝ}
    (law : ∀ z∈(e.symm.trans d).source, f z = ‖deriv (e.symm.trans d) z‖^2*g ((e.symm.trans d) z)) :
    (∫ z in e.target, (ρ (e.symm z)*σ (e.symm z))*f z) =
      ∫ z in d.target, (σ (d.symm z)*ρ (d.symm z))*g z := by
  let t := e.symm.trans d
  have first : (∫ z in e.target, (ρ (e.symm z)*σ (e.symm z))*f z) =
      ∫ z in t.source, (ρ (e.symm z)*σ (e.symm z))*f z := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero e.open_target.measurableSet (fun z hz => hz.1)
    intro z hz
    have out : e.symm z ∉ tsupport σ := fun mem => hz.2 ⟨hz.1,sd mem⟩
    simp [image_eq_zero_of_notMem_tsupport out]
  have second : (∫ z in d.target, (σ (d.symm z)*ρ (d.symm z))*g z) =
      ∫ z in t.target, (σ (d.symm z)*ρ (d.symm z))*g z := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero d.open_target.measurableSet (fun z hz => hz.1)
    intro z hz
    have out : d.symm z ∉ tsupport ρ := fun mem => hz.2 ⟨hz.1,se mem⟩
    simp [image_eq_zero_of_notMem_tsupport out]
  rw [first,second,← t.image_source_eq_target,integral_image_eq_integral_abs_det_fderiv_smul volume t.open_source.measurableSet
    (fun z hz => ((compact_cover_transition he hd hz).analyticAt.differentiableAt.restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt)
    t.injOn]
  apply setIntegral_congr_fun t.open_source.measurableSet
  intro z hz
  change (ρ (e.symm z)*σ (e.symm z))*f z= |(fderiv ℝ t z).det| • ((σ (d.symm (t z))*ρ (d.symm (t z)))*g (t z))
  rw [compact_cover_jacobian (compact_cover_transition he hd hz).analyticAt.differentiableAt,
    abs_of_nonneg (sq_nonneg _),show d.symm (t z)=e.symm z from d.left_inv hz.2,law z hz,smul_eq_mul]
  ring

/-- Chart densities integrated against a finite cover of their support
give the same real number in every other such cover. -/
theorem compact_test_integral_independent {M : Type u} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {K : Set M} (P Q : CompactTestChartCover K)
    (f : OpenPartialHomeomorph M ℂ → ℂ → ℝ)
    (ct : ∀ e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M, ContinuousOn (f e) e.target)
    (off : ∀ e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M, ∀ z∈e.target, e.symm z∉K → f e z=0)
    (law : ∀ e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M, ∀ d∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M,
      ∀ z∈(e.symm.trans d).source, f e z=‖deriv (e.symm.trans d) z‖^2*f d ((e.symm.trans d) z)) :
    P.integral f=Q.integral f := by
  classical
  let J (e : OpenPartialHomeomorph M ℂ) (w : M → ℝ) := ∫ z in e.target, w (e.symm z)*f e z
  have split (R S : CompactTestChartCover K) (i : R.indices) :
      J (R.chart i) (R.weight i)=∑ j, J (R.chart i) (fun p => R.weight i p*S.weight j p) := by
    let e := R.chart i
    let B := e '' tsupport (R.weight i)
    have cB : IsCompact B := (R.compact i).image_of_continuousOn (e.continuousOn.mono (R.supported i))
    have sub : B ⊆ e.target := by rintro _ ⟨p,hp,rfl⟩; exact e.map_source (R.supported i hp)
    have int (j : S.indices) : IntegrableOn
        (fun z => (R.weight i (e.symm z)*S.weight j (e.symm z))*f e z) e.target := by
      have cont := (((R.smooth i).continuous.comp_continuousOn e.continuousOn_symm).mul
        ((S.smooth j).continuous.comp_continuousOn e.continuousOn_symm)).mul (ct e (R.member i))
      apply ((cont.mono sub).integrableOn_compact cB).of_forall_sdiff_eq_zero e.open_target.measurableSet
      intro z hz
      have away : e.symm z∉tsupport (R.weight i) := fun mem => hz.2 ⟨_,mem,e.right_inv hz.1⟩
      simp [image_eq_zero_of_notMem_tsupport away]
    dsimp only [J]
    rw [← integral_finsetSum _ (fun j _ => int j)]
    apply setIntegral_congr_fun e.open_target.measurableSet
    intro z hz
    change R.weight i (e.symm z)*f e z = ∑ j, (R.weight i (e.symm z)*S.weight j (e.symm z))*f e z
    by_cases mem : e.symm z ∈ K
    · simp only [← Finset.sum_mul,← Finset.mul_sum,S.unity _ mem,mul_one]
    · simp [off e (R.member i) z hz mem]
  have swap (i : P.indices) (j : Q.indices) :
      J (P.chart i) (fun p => P.weight i p*Q.weight j p) =
        J (Q.chart j) (fun p => Q.weight j p*P.weight i p) :=
    compact_test_swap (P.member i) (Q.member j) (P.supported i) (Q.supported j)
      (law _ (P.member i) _ (Q.member j))
  change (∑ i, J (P.chart i) (P.weight i))=∑ j, J (Q.chart j) (Q.weight j)
  simp_rw [split P Q,swap]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => (split Q P j).symm)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.exists_compact_test_chart_cover
#print axioms TwoAxisHelicoid.compact_test_integral_independent
