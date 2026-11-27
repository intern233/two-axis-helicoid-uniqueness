import TwoAxisHelicoid.DisjointTorusCoreObstruction
import TwoAxisHelicoid.CompactMovingPreimage
import TwoAxisHelicoid.IntersectingCompactCoresOnPuncture

namespace TwoAxisHelicoid
open Set Metric Filter Topology
open scoped Topology

/-- Through every point of the punctured torus there is a compact connected
set meeting its image under every homeomorphism. -/
theorem punctured_torus_compact_core_meets_images {M : Type*} [TopologicalSpace M] [T2Space M]
    {A : PeriodPair} (mark : M ≃ₜ PuncturedPeriodTorus A) (p : M) :
    ∃ K : Set M, IsCompact K ∧ IsConnected K ∧ p ∈ K ∧
      ∀ d : M ≃ₜ M, ∃ a ∈ K, d a ∈ K := by
  classical
  let := periodTorus_compactSpace A
  let : T1Space (PeriodTorus A) := QuotientAddGroup.t1Space_iff.mpr A.isClosed_lattice
  let := punctured_torus_is_path_connected A
  let : PathConnectedSpace M := mark.symm.surjective.pathConnectedSpace mark.symm.continuous
  obtain ⟨C⟩ := exists_torus_generating_core_model A
  let := C.pathConnected
  exact intersecting_compact_cores_on_puncture (0 : PeriodTorus A) mark C.carrier
    C.isOpen_carrier C.closure_avoids C.base (disjoint_genus_one_cores_impossible C C) p

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.punctured_torus_compact_core_meets_images
#print axioms TwoAxisHelicoid.compact_core_confines_reflected_parameter
#print axioms TwoAxisHelicoid.continuousAt_of_compact_moving_preimage
