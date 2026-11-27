import Mathlib.Topology.Compactification.OnePoint.Basic

namespace TwoAxisHelicoid
open Set Topology

/-- A compact Hausdorff space is the one-point compactification of the
complement of any chosen point. -/
noncomputable def punctureCompactification {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] (p : X) : OnePoint {x : X // x ≠ p} ≃ₜ X :=
  OnePoint.equivOfIsEmbeddingOfRangeEq p Subtype.val IsEmbedding.subtypeVal
    (by ext x; simp)

/-- Extend a homeomorphism of punctured compact surfaces across their ends. -/
noncomputable def compactPunctureExtension {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] {p : X} {q : Y}
    (h : {x : X // x ≠ p} ≃ₜ {y : Y // y ≠ q}) : X ≃ₜ Y :=
  (punctureCompactification p).symm.trans (h.onePointCongr.trans (punctureCompactification q))

theorem compactPunctureExtension_at_end {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] {p : X} {q : Y}
    (h : {x : X // x ≠ p} ≃ₜ {y : Y // y ≠ q}) : compactPunctureExtension h p = q := by
  have h0 : (punctureCompactification p) OnePoint.infty = p := rfl
  change punctureCompactification q (h.onePointCongr ((punctureCompactification p).symm p)) = q
  rw [(punctureCompactification p).symm_apply_eq.mpr h0.symm]
  rfl

theorem compactPunctureExtension_apply {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] {p : X} {q : Y}
    (h : {x : X // x ≠ p} ≃ₜ {y : Y // y ≠ q}) (x : {x : X // x ≠ p}) :
    compactPunctureExtension h x = h x := by
  have hx : punctureCompactification p (x : OnePoint {x : X // x ≠ p}) = x := rfl
  change punctureCompactification q (h.onePointCongr ((punctureCompactification p).symm x.1)) = _
  rw [(punctureCompactification p).symm_apply_eq.mpr hx.symm]
  rfl

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.compactPunctureExtension_apply
