import TwoAxisHelicoid.FlatEndCompactification

namespace TwoAxisHelicoid
open Set

noncomputable def puncturedCapMap {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    (p : M) (A H : ℝ) (X : {q : M // q ≠ p} → HelicoidTubeCoordinates) : M → HelicoidTubeCoordinates :=
  cappedOnePointMap A H X ∘ (punctureOnePointHomeomorph p).symm

theorem puncturedCapMap_at_puncture {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    (p : M) (A H : ℝ) (X : {q : M // q ≠ p} → HelicoidTubeCoordinates) :
    puncturedCapMap p A H X p = planeCapNorth H := by
  let e := punctureOnePointHomeomorph p
  have he : e (OnePoint.infty : OnePoint {q : M // q ≠ p}) = p := rfl
  have hb : e.symm p = OnePoint.infty := by
    simpa only [e.symm_apply_apply] using (congrArg e.symm he).symm
  change cappedOnePointMap A H X (e.symm p) = planeCapNorth H
  rw [hb]
  rfl

theorem puncturedCapMap_on_punctured {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    (p : M) (A H : ℝ) (X : {q : M // q ≠ p} → HelicoidTubeCoordinates) (q : {q : M // q ≠ p}) :
    puncturedCapMap p A H X q.1 = ambientPlaneCap A H (X q) := by
  let e := punctureOnePointHomeomorph p
  have he : e (q : OnePoint {q : M // q ≠ p}) = q.1 := rfl
  change cappedOnePointMap A H X (e.symm q.1) = ambientPlaneCap A H (X q)
  rw [← he,e.symm_apply_apply]
  rfl

theorem puncturedCapMap_isClosedEmbedding {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    {p : M} {X : {q : M // q ≠ p} → HelicoidTubeCoordinates}
    (hX : IsProperMap X) (hXi : Function.Injective X)
    {A H R : ℝ} (hR : 0 < R) (hA1 : 1 ≤ A) (hAR : 4*R^2 ≤ A) (hH : 4*R ≤ H)
    (hflat : ∀ y ∈ range X, R^2 < ambientRadiusSq y → y.1.2 = 0) :
    Topology.IsClosedEmbedding (puncturedCapMap p A H X) :=
  (cappedOnePointMap_isClosedEmbedding hX hXi hR hA1 hAR hH hflat).comp
    (punctureOnePointHomeomorph p).symm.isClosedEmbedding

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.puncturedCapMap_isClosedEmbedding
