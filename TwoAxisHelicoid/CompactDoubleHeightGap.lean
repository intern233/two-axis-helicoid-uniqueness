import TwoAxisHelicoid.CertifiedCompactDoublePoints

namespace TwoAxisHelicoid
open Set Topology Metric
open scoped Topology

/-- When the double-point pairs are compact, a simple complete height
level lies inside a closed slab free from any spatial collision. -/
theorem compact_double_height_gap {M E : Type*} [TopologicalSpace M] [TopologicalSpace E] {X : M → E}
    (proper : IsProperMap X) (dc : IsCompact (immersionDoublePoints X)) (h : E → ℝ) (ch : Continuous h)
    (s : ℝ) (simple : InjOn X {u | h (X u)=s}) :
    ∃ ε R : ℝ, 0<ε ∧ ε<R ∧
      (∀ q∈immersionDoublePoints X, |h (X q.1)-s|∈Ioo ε R) ∧
      IsClosedEmbedding (fun u : {u : M | |h (X u)-s|≤ε} => X u.1) := by
  let f := fun u : M => |h (X u)-s|
  have cf : Continuous f := ((ch.comp proper.continuous).sub continuous_const).abs
  let heights := (fun q : M × M => f q.1) '' immersionDoublePoints X
  have hc : IsCompact heights := dc.image (cf.comp continuous_fst)
  have miss : (0:ℝ)∉heights := by
    rintro ⟨⟨u,v⟩,⟨same,ne⟩,eq⟩
    have level : h (X u)=s := sub_eq_zero.mp (abs_eq_zero.mp eq)
    exact ne (simple level (by change h (X v)=s; rwa [← same]) same)
  obtain ⟨δ,dp,away⟩ := Metric.mem_nhds_iff.mp (hc.isClosed.isOpen_compl.mem_nhds miss)
  obtain ⟨b,bd⟩ := hc.bddAbove
  let ε := δ/2
  let R := max b ε+1
  have ep : 0<ε := half_pos dp
  have er : ε<R := by dsimp [R]; linarith [le_max_right b ε]
  have bound {u v : M} (p : (u,v)∈immersionDoublePoints X) : f u∈Ioo ε R := by
    have hit : f u∈heights := ⟨(u,v),p,rfl⟩
    have nonneg : 0≤f u := abs_nonneg _
    have lower : δ≤f u := by
      by_contra! lt
      exact (away (show f u∈ball 0 δ by simpa [Real.dist_eq,abs_of_nonneg nonneg] using lt)) hit
    exact ⟨(half_lt_self dp).trans_le lower,(bd hit).trans_lt (by dsimp [R]; linarith [le_max_left b ε])⟩
  have closed : IsClosed {u | f u≤ε} := isClosed_le cf continuous_const
  refine ⟨ε,R,ep,er,fun _ p => bound p,?_⟩
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap (proper.continuous.comp continuous_subtype_val) _
    (proper.isClosedMap.comp closed.isClosedEmbedding_subtypeVal.isClosedMap)
  intro u v eq
  apply Subtype.ext
  by_contra ne
  exact (not_lt_of_ge u.2) (bound (show (u.1,v.1)∈immersionDoublePoints X from ⟨eq,ne⟩)).1

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_double_height_gap
