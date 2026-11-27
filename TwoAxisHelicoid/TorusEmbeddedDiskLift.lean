import TwoAxisHelicoid.CompactEmbeddedCoverLift
import TwoAxisHelicoid.TorusActualLifts
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace TwoAxisHelicoid
open Set Metric Topology

/-- An arbitrary embedded closed topological disk in the marked torus
has a single lift inside an open planar chart of the lattice covering. -/
theorem embedded_torus_disk_has_injective_planar_neighborhood (L : PeriodPair)
    (u : C(closedBall (0:ℂ) 1,PeriodTorus L)) (emb : IsEmbedding u) :
    ∃ (F : C(closedBall (0:ℂ) 1,ℂ)) (V : Set ℂ), (∀ z, periodTorusProjection L (F z)=u z) ∧
      IsEmbedding F ∧ IsOpen V ∧ range F⊆V ∧ IsOpenEmbedding (V.domRestrict (periodTorusProjection L)) := by
  let _ : T1Space (PeriodTorus L) := QuotientAddGroup.t1Space_iff.mpr L.isClosed_lattice
  let a : closedBall (0:ℂ) 1 := ⟨0,mem_closedBall_self zero_le_one⟩
  let _ : ContractibleSpace (closedBall (0:ℂ) 1) :=
    (convex_closedBall (0:ℂ) 1).contractibleSpace ⟨a.1,a.2⟩
  let _ : LocallyPathConnectedSpace (closedBall (0:ℂ) 1) :=
    (convex_closedBall (0:ℂ) 1).locallyPathConnectedSpace
  obtain ⟨v,hv⟩ := (Quotient.mk_surjective : Function.Surjective (periodTorusProjection L)) (u a)
  obtain ⟨F,V,_,lift,injection,op,inside,sheet⟩ := compact_embedding_lifts_into_open_sheet
    (periodTorusProjection_isCoveringMap L) u emb a v hv
  exact ⟨F,V,lift,injection,op,inside,sheet⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.embedded_torus_disk_has_injective_planar_neighborhood
