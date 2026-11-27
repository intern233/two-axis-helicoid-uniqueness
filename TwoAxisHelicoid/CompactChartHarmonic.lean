import TwoAxisHelicoid.HarmonicLocalMaximum
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Connected.Clopen

namespace TwoAxisHelicoid
open Complex Set Filter InnerProductSpace
open scoped Topology

/-- Harmonicity in the chosen complex coordinate charts. This hypothesis is the
ordinary local harmonicity condition; it is not a claim that an unconstructed
period primitive exists. -/
def HarmonicInComplexCharts {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (u : X → ℝ) : Prop :=
  ∀ p : X, HarmonicAt (fun z : ℂ => u ((chartAt ℂ p).symm z)) (chartAt ℂ p p)

theorem compact_connected_chart_harmonic_constant {X : Type*}
    [TopologicalSpace X] [ChartedSpace ℂ X] [CompactSpace X] [PreconnectedSpace X]
    {u : X → ℝ} (hu : Continuous u) (hh : HarmonicInComplexCharts u) :
    ∀ x y : X, u x = u y := by
  intro x y
  obtain ⟨p,_,hp⟩ := isCompact_univ.exists_isMaxOn
    (show (univ : Set X).Nonempty from ⟨x,mem_univ x⟩) hu.continuousOn
  let S : Set X := {q | u q = u p}
  have hclosed : IsClosed S := isClosed_eq hu continuous_const
  have hopen : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro q hq
    have hq' : u q = u p := hq
    let e := chartAt ℂ q
    have heq : e.symm (e q) = q := e.left_inv (mem_chart_source ℂ q)
    have hm : IsLocalMax (fun z : ℂ => u (e.symm z)) (e q) := by
      apply Filter.Eventually.of_forall
      intro z
      change u (e.symm z) ≤ u (e.symm (e q))
      rw [heq]
      exact (hp (mem_univ (e.symm z))).trans_eq hq'.symm
    have hc := harmonic_eventually_constant_at_local_max (hh q) hm
    have hec : ContinuousAt e q := e.continuousAt (mem_chart_source ℂ q)
    have hpull := hec.eventually hc
    filter_upwards [hpull,chart_source_mem_nhds ℂ q] with w hw hws
    change u w = u p
    rw [e.left_inv hws,heq] at hw
    exact hw.trans hq'
  have hS : S = univ := (show IsClopen S from ⟨hclosed,hopen⟩).eq_univ
    ⟨p,(rfl : u p = u p)⟩
  have hx : x ∈ S := by rw [hS]; exact mem_univ x
  have hy : y ∈ S := by rw [hS]; exact mem_univ y
  exact hx.trans hy.symm

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.compact_connected_chart_harmonic_constant
