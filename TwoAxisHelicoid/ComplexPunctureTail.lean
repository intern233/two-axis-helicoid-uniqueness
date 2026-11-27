import TwoAxisHelicoid.PuncturedDiskPolygon
import Mathlib.Geometry.Manifold.ChartedSpace

namespace TwoAxisHelicoid
open Complex Set Metric Filter
open scoped Topology
set_option maxHeartbeats 1000000

/-- A complex chart supplies arbitrarily small punctured connected
neighborhoods, without any global uniformization assumption. -/
theorem complex_chart_connected_punctured_neighborhood {M : Type*}
    [TopologicalSpace M] [ChartedSpace ℂ M] (p : M) {V : Set M}
    (hV : IsOpen V) (hp : p ∈ V) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ U ⊆ V ∧ IsPreconnected (U \ {p}) := by
  let e := chartAt ℂ p
  have hps : p ∈ e.source := mem_chart_source ℂ p
  have hW : IsOpen (e.target ∩ e.symm ⁻¹' V) := e.symm.isOpen_inter_preimage hV
  have heW : e p ∈ e.target ∩ e.symm ⁻¹' V :=
    ⟨e.map_source hps,by simpa only [mem_preimage,e.left_inv hps] using hp⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds heW)
  let U : Set M := e.source ∩ e ⁻¹' ball (e p) r
  have hU : IsOpen U := e.isOpen_inter_preimage isOpen_ball
  have hpU : p ∈ U := ⟨hps,mem_ball_self hr⟩
  have hUV : U ⊆ V := by
    intro q hq
    simpa only [mem_preimage,e.left_inv hq.1] using (hball hq.2).2
  have hconn := complex_ball_diff_finite_isPreconnected (e p) hr (finite_singleton (e p))
  have htarget : ball (e p) r \ {e p} ⊆ e.target := fun _ hz => (hball hz.1).1
  have hi := hconn.image e.symm (e.continuousOn_symm.mono htarget)
  have heq : e.symm '' (ball (e p) r \ {e p}) = U \ {p} := by
    ext q
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨⟨e.map_target (htarget hz),?_⟩,?_⟩
      · change e (e.symm z) ∈ ball (e p) r
        rw [e.right_inv (htarget hz)]
        exact hz.1
      · intro hqp
        have hq : e.symm z = p := hqp
        apply hz.2
        change z = e p
        rw [← e.right_inv (htarget hz),hq]
    · rintro ⟨hqU,hqp⟩
      refine ⟨e q,⟨hqU.2,?_⟩,e.left_inv hqU.1⟩
      intro heq
      exact hqp (e.injOn hqU.1 hps heq)
  exact ⟨U,hU,hpU,hUV,heq ▸ hi⟩

/-- Deleting one point from a compact complex curve gives connected
subends beyond every prescribed compact set. The complement of each
chosen subend is compact in the punctured curve itself. -/
theorem compact_complex_puncture_connected_tail {M : Type*}
    [TopologicalSpace M] [ChartedSpace ℂ M] [CompactSpace M] [T2Space M]
    (p : M) {K : Set {q : M // q ≠ p}} (hK : IsCompact K) :
    ∃ U : Set {q : M // q ≠ p}, IsOpen U ∧ IsPreconnected U ∧
      IsCompact Uᶜ ∧ Disjoint U K := by
  let C : Set M := Subtype.val '' K
  have hC : IsCompact C := hK.image continuous_subtype_val
  have hpC : p ∉ C := by
    rintro ⟨q,_hq,hqp⟩
    exact q.2 hqp
  obtain ⟨V,hV,hpV,hVC,hconn⟩ := complex_chart_connected_punctured_neighborhood p
    hC.isClosed.isOpen_compl hpC
  let U : Set {q : M // q ≠ p} := Subtype.val ⁻¹' V
  refine ⟨U,hV.preimage continuous_subtype_val,?_,?_,?_⟩
  · have hc := hconn.preimage_of_isOpenMap Subtype.val_injective
      (isOpen_compl_singleton.isOpenMap_subtype_val) (by
        intro q hq
        exact ⟨⟨q,hq.2⟩,rfl⟩)
    have heq : (Subtype.val ⁻¹' (V \ {p}) : Set {q : M // q ≠ p}) = U := by
      ext q
      simp [U,q.2]
    exact heq ▸ hc
  · rw [Subtype.isCompact_iff]
    have heq : Subtype.val '' Uᶜ = Vᶜ := by
      ext q
      constructor
      · rintro ⟨z,hz,rfl⟩
        exact hz
      · intro hq
        refine ⟨⟨q,?_⟩,hq,rfl⟩
        rintro rfl
        exact hq hpV
    rw [heq]
    exact hV.isClosed_compl.isCompact
  · apply Set.disjoint_left.mpr
    intro q hqU hqK
    exact hVC hqU ⟨q,hqK,rfl⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.compact_complex_puncture_connected_tail
