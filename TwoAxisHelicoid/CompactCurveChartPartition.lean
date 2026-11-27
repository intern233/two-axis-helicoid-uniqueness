import TwoAxisHelicoid.SmoothMarkedCircleClass
import Mathlib.Geometry.Manifold.PartitionOfUnity

namespace TwoAxisHelicoid
open Complex Set Filter Topology Function
open scoped Topology Manifold ContDiff

/-- A compact Riemann surface admits a finite smooth partition with
compact supports contained in its actual coordinate charts. -/
theorem compact_curve_chart_partition (M : Type*) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] :
    ∃ (C : Finset M) (ρ : C → M → ℝ),
      (∀ x, ∑ i, ρ i x=1) ∧ (∀ i x, 0≤ρ i x) ∧
      (∀ i, ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ) ∞ (ρ i)) ∧
      ∀ i, IsCompact (tsupport (ρ i)) ∧ tsupport (ρ i)⊆(chartAt ℂ i.1).source := by
  classical
  let _ := complex_curve_underlying_real_manifold M
  let U := fun x : M => (chartAt ℂ x).source
  obtain ⟨C,all⟩ := isCompact_univ.elim_finite_subcover U (fun x => (chartAt ℂ x).open_source)
    (show (univ : Set M)⊆⋃ x, U x from fun x _ => mem_iUnion.mpr ⟨x,mem_chart_source ℂ x⟩)
  have cv : (univ : Set M)⊆⋃ i : C, U i.1 := by
    intro x hx
    obtain ⟨i,hi,inside⟩ := mem_iUnion₂.mp (all hx)
    exact mem_iUnion.mpr ⟨⟨i,hi⟩,inside⟩
  obtain ⟨ρ,sub⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ,ℂ) isClosed_univ (fun i : C => U i.1)
    (fun i => (chartAt ℂ i.1).open_source) cv
  exact ⟨C,fun i => ρ i,fun x => by simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x),
    ρ.nonneg,fun i => (ρ i).contMDiff,fun i => ⟨(isClosed_tsupport (ρ i)).isCompact,sub i⟩⟩

/-- Extend a coefficient already supported on a compact subset of a
chart by zero. The extension is globally C¹ and its full derivative
agrees with the local coefficient throughout the chart domain. -/
theorem extend_compact_chart_coefficient {D K : Set ℂ} (op : IsOpen D) (compact : IsCompact K)
    (inside : K⊆D) {f : ℂ → ℂ} (sm : ∀ z∈D, ContDiffAt ℝ 1 f z)
    (zero : ∀ z∈D, z∉K → f z=0) :
    ∃ g : ℂ → ℂ, ContDiff ℝ 1 g ∧ HasCompactSupport g ∧ tsupport g ⊆ K ∧
      (∀ z∈D, g =ᶠ[𝓝 z] f) ∧ ∀ z∉K, g =ᶠ[𝓝 z] 0 := by
  classical
  let g := D.indicator f
  have agree (z : ℂ) (hz : z∈D) : g =ᶠ[𝓝 z] f := by
    filter_upwards [op.mem_nhds hz] with w hw
    exact indicator_of_mem hw f
  have empty (z : ℂ) (hz : z∉K) : g =ᶠ[𝓝 z] 0 := by
    filter_upwards [compact.isClosed.isOpen_compl.mem_nhds hz] with w hw
    by_cases dw : w∈D
    · exact (indicator_of_mem dw f).trans (zero w dw hw)
    · exact indicator_of_notMem dw f
  have sub : tsupport g⊆K := by
    intro z hz
    by_contra out
    exact (notMem_tsupport_iff_eventuallyEq.mpr (empty z out)) hz
  refine ⟨g,contDiff_iff_contDiffAt.mpr ?_,compact.of_isClosed_subset (isClosed_tsupport g) sub,sub,agree,empty⟩
  intro z
  by_cases hz : z∈K
  · exact (sm z (inside hz)).congr_of_eventuallyEq (agree z (inside hz))
  · exact (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq (empty z hz)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_curve_chart_partition
#print axioms TwoAxisHelicoid.extend_compact_chart_coefficient
