import TwoAxisHelicoid.SimpleImmersionHeightContacts
import TwoAxisHelicoid.RegularCutHalfPlaneCharts
import TwoAxisHelicoid.EquivariantTorusFrame
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

namespace TwoAxisHelicoid
open Complex Set Topology MeasureTheory Filter InnerProductSpace
open scoped Topology ContDiff RealInnerProductSpace

/-- At a fixed regular point of a spatial immersion at most one
finite plane slope has its tangent plane. -/
theorem ae_tilted_height_regular_at_point {F : ℂ → Fin 3 → ℝ} {z : ℂ}
    (diff : DifferentiableAt ℝ F z) (imm : Function.Injective (fderiv ℝ F z)) :
    ∀ᵐ s : ℂ, fderiv ℝ (tiltedSpatialHeight s ∘ F) z≠0 := by
  by_cases ex : ∃ s : ℂ, fderiv ℝ (tiltedSpatialHeight s ∘ F) z=0
  · obtain ⟨c,cri⟩ := ex
    have one := (tilted_contact_iff diff c).mp cri
    let D := (spatialGraphProjection 0 1).comp (fderiv ℝ F z)
    have onto : Function.Surjective D :=
      (LinearMap.injective_iff_surjective (f:=D.toLinearMap)).mp (horizontal_projection_injective_at_height_contact imm c one)
    filter_upwards [volume.ae_ne c] with s distinct
    intro same
    have two := (tilted_contact_iff diff s).mp same
    apply distinct
    apply ext_inner_right ℝ
    intro w
    obtain ⟨v,rfl⟩ := onto w
    exact (two v).symm.trans (one v)
  · exact Filter.Eventually.of_forall fun _ h => ex ⟨_,h⟩

/-- A height submersion in one true parameter on a surface gives a
chart whose second coordinate is the actual, unshifted height. -/
theorem surface_height_chart_of_parameter {M : Type*} [TopologicalSpace M]
    {p : M} {h : M → ℝ} (d : OpenPartialHomeomorph M ℂ) (src : p∈d.source)
    (smooth : ContDiffAt ℝ ∞ (h ∘ d.symm) (d p))
    (regular : fderiv ℝ (h ∘ d.symm) (d p)≠0) :
    ∃ e : OpenPartialHomeomorph M (ℝ×ℝ), p∈e.source ∧ ∀ w∈e.target, h (e.symm w)=w.2 := by
  have reg : ∃ w, fderiv ℝ (h ∘ d.symm) (d p) w≠0 := by
    by_contra! all
    exact regular (ContinuousLinearMap.ext all)
  obtain ⟨a,asrc,coord,_,_⟩ := regular_real_level_coordinate smooth reg
  let flip := (Homeomorph.prodComm ℝ ℝ).toOpenPartialHomeomorph
  let e := (d.trans a).trans flip
  have present : p∈e.source := ⟨⟨src,asrc⟩,mem_univ _⟩
  have hcoord (y : M) (hy : y∈e.source) : (e y).2=h y := by
    change (a (d y)).1=h y
    rw [coord,Function.comp_apply,d.left_inv hy.1.1]
  refine ⟨e,present,?_⟩
  intro w hw
  rw [← hcoord _ (e.map_target hw),e.right_inv hw]

/-- The marked torus projection carries an unmarked smooth regular
plane height germ to a height chart in the torus itself. -/
theorem torus_height_chart_of_regular_lift (L : PeriodPair) {h : PeriodTorus L → ℝ} (z : ℂ)
    (smooth : ContDiffAt ℝ ∞ (h ∘ periodTorusProjection L) z)
    (regular : fderiv ℝ (h ∘ periodTorusProjection L) z≠0) :
    ∃ e : OpenPartialHomeomorph (PeriodTorus L) (ℝ×ℝ), periodTorusProjection L z∈e.source ∧
      ∀ w∈e.target, h (e.symm w)=w.2 := by
  obtain ⟨d,src,repr⟩ := periodTorusProjection_isLocalHomeomorph L z
  have projected := congrFun repr z
  have hit : periodTorusProjection L z∈d.target := projected ▸ d.map_source src
  have atPoint : d.symm (periodTorusProjection L z)=z := by rw [projected,d.left_inv src]
  apply surface_height_chart_of_parameter d.symm hit
  · change ContDiffAt ℝ ∞ (h ∘ d) (d.symm (periodTorusProjection L z))
    rwa [atPoint,← repr]
  · change fderiv ℝ (h ∘ d) (d.symm (periodTorusProjection L z))≠0
    rwa [atPoint,← repr]

/-- The marked point can be tested in any regular spatial chart, with
no differentiability comparison to the punctured conformal marking. -/
theorem ae_tilted_surface_height_chart_at_mark {M : Type*} [TopologicalSpace M]
    (F : M → Fin 3 → ℝ) (p : M) (d : OpenPartialHomeomorph M ℂ) (src : p∈d.source)
    (smooth : ContDiffAt ℝ ∞ (F ∘ d.symm) (d p))
    (imm : Function.Injective (fderiv ℝ (F ∘ d.symm) (d p))) :
    ∀ᵐ s : ℂ, ∃ e : OpenPartialHomeomorph M (ℝ×ℝ), p∈e.source ∧
      ∀ w∈e.target, tiltedSpatialHeight s (F (e.symm w))=w.2 := by
  filter_upwards [ae_tilted_height_regular_at_point (smooth.differentiableAt (by simp)) imm] with s reg
  exact surface_height_chart_of_parameter (h:=tiltedSpatialHeight s ∘ F) d src
    ((tiltedSpatialHeight s).contDiff.contDiffAt.comp _ smooth) reg

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.ae_tilted_surface_height_chart_at_mark
#print axioms TwoAxisHelicoid.torus_height_chart_of_regular_lift
