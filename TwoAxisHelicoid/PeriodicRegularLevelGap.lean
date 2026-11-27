import TwoAxisHelicoid.PeriodTorusTopology
import Mathlib.Topology.Order.Compact

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- A periodic differential with poles at the lattice is uniformly
nonzero wherever the periodic height avoids its critical value.
Clipping its norm at one gives a continuous positive test function
through the poles, irrespective of the height behavior there. -/
theorem periodic_regular_level_gap (L : PeriodPair) (f : ℂ → ℂ) (h : ℂ → ℝ)
    (cf : ∀ z∉L.lattice, ContinuousAt f z) (ch : ∀ z∉L.lattice, ContinuousAt h z)
    (pf : ∀ z w, w∈L.lattice → f (z+w)=f z) (ph : ∀ z w, w∈L.lattice → h (z+w)=h z)
    (pole : ∀ w∈L.lattice, Tendsto (fun z => ‖f z‖) (𝓝[≠] w) atTop)
    (critical : ∀ z∉L.lattice, f z=0 → h z=0) {ε : ℝ} (positive : 0<ε) :
    ∃ δ>0, ∀ z∉L.lattice, ε≤|h z| → δ≤‖f z‖ := by
  classical
  let A := fun z : ℂ => max (min 1 ‖f z‖) (min 1 (max 0 (ε-|h z|)))
  let T := fun z : ℂ => if z∈L.lattice then 1 else A z
  have eq (p : ℂ) (hp : p∉L.lattice) : T =ᶠ[𝓝 p] A := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hp] with z hz using ite_eq_right hz
  have cont : Continuous T := continuous_iff_continuousAt.mpr (by
    intro z
    by_cases hL : z∈L.lattice
    · apply continuousAt_iff_punctured_nhds.mpr
      have same : T =ᶠ[𝓝[≠] z] (fun _ => (1:ℝ)) := by
        filter_upwards [(pole z hL).eventually_ge_atTop 1] with x hx
        by_cases inL : x∈L.lattice
        · simp [T,inL]
        · simp [T,A,inL,min_eq_left hx]
      simpa only [T,ite_eq_left hL] using (tendsto_const_nhds (x := (1:ℝ))).congr' same.symm
    · have ca : ContinuousAt A z :=
        (continuousAt_const.min (cf z hL).norm).max
          (continuousAt_const.min (continuousAt_const.max (continuousAt_const.sub (ch z hL).abs)))
      exact ca.congr_of_eventuallyEq (eq z hL))
  have per (z w : ℂ) (hw : w∈L.lattice) : T (z+w)=T z := by
    have equiv : z+w∈L.lattice ↔ z∈L.lattice := ⟨fun hz => by simpa using L.lattice.sub_mem hz hw,
      fun hz => L.lattice.add_mem hz hw⟩
    simp only [T,A,equiv,pf z w hw,ph z w hw]
  have pos (z : ℂ) : 0<T z := by
    by_cases hL : z∈L.lattice
    · simp [T,hL]
    rw [show T z=A z from ite_eq_right hL]
    by_cases hf : f z=0
    · apply lt_of_lt_of_le _ (le_max_right _ _)
      simpa [critical z hL hf,positive.le] using (lt_min (by norm_num : (0:ℝ)<1) positive)
    · exact lt_of_lt_of_le (lt_min zero_lt_one (norm_pos_iff.mpr hf)) (le_max_left _ _)
  have compact := IsZLattice.isCompact_range_of_periodic L.lattice T cont per
  obtain ⟨v,⟨x,rfl⟩,minimum⟩ := compact.exists_isMinOn (range_nonempty T) continuous_id.continuousOn
  refine ⟨T x,pos x,?_⟩
  intro z hz hy
  have below : T x≤T z := minimum (mem_range_self z)
  have a : max 0 (ε-|h z|)=0 := max_eq_left (sub_nonpos.mpr hy)
  apply below.trans
  simp only [T,ite_eq_right hz,A,a,min_eq_right zero_le_one,max_eq_left (le_min zero_le_one (norm_nonneg _))]
  exact min_le_right _ _

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.periodic_regular_level_gap
