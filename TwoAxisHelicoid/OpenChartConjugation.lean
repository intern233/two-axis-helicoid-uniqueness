import Mathlib.Topology.OpenPartialHomeomorph.Basic

namespace TwoAxisHelicoid
open Set

theorem homeomorph_symm_mem_iff {X : Type*} [TopologicalSpace X]
    (H : X ≃ₜ X) {U : Set X} (hH : ∀ x, x ∈ U ↔ H x ∈ U) (x : X) :
    H.symm x ∈ U ↔ x ∈ U := by
  simpa only [Homeomorph.apply_symm_apply] using hH (H.symm x)

/-- Transport an actual global coordinate homeomorphism through an open
chart. Source and target are exactly the chart's open image. -/
noncomputable def conjugateChartHomeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) (H : X ≃ₜ X)
    (hH : ∀ x, x ∈ e.source ↔ H x ∈ e.source) : OpenPartialHomeomorph Y Y where
  toFun := fun y => e (H (e.symm y))
  invFun := fun y => e (H.symm (e.symm y))
  source := e.target
  target := e.target
  map_source' y hy := e.map_source ((hH _).mp (e.map_target hy))
  map_target' y hy := e.map_source ((homeomorph_symm_mem_iff H hH _).mpr (e.map_target hy))
  left_inv' y hy := by
    have hHs := (hH _).mp (e.map_target hy)
    rw [e.left_inv hHs,Homeomorph.symm_apply_apply,e.right_inv hy]
  right_inv' y hy := by
    have hHs := (homeomorph_symm_mem_iff H hH _).mpr (e.map_target hy)
    rw [e.left_inv hHs,Homeomorph.apply_symm_apply,e.right_inv hy]
  open_source := e.open_target
  open_target := e.open_target
  continuousOn_toFun := e.continuousOn.comp (H.continuous.comp_continuousOn e.continuousOn_symm)
    (fun y hy => (hH _).mp (e.map_target hy))
  continuousOn_invFun := e.continuousOn.comp (H.symm.continuous.comp_continuousOn e.continuousOn_symm)
    (fun y hy => (homeomorph_symm_mem_iff H hH _).mpr (e.map_target hy))

theorem conjugateChartHomeomorph_fixes {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) (H : X ≃ₜ X)
    (hH : ∀ x, x ∈ e.source ↔ H x ∈ e.source) {y : Y} (hy : y ∈ e.target)
    (hfix : H (e.symm y) = e.symm y) : conjugateChartHomeomorph e H hH y = y := by
  change e (H (e.symm y)) = y
  rw [hfix,e.right_inv hy]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.conjugateChartHomeomorph
