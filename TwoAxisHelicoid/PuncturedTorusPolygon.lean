import TwoAxisHelicoid.PuncturedDiskPolygon
import TwoAxisHelicoid.PeriodTorusConjugation
import TwoAxisHelicoid.PuncturedLatticePlane

namespace TwoAxisHelicoid
open Complex Set

namespace PlanePolygon

theorem source_mem {Ω : Set ℂ} {x y : ℂ} (p : PlanePolygon Ω x y) : x ∈ Ω := by
  induction p with
  | refl _ h => exact h
  | step a b h => simpa using h 0 (by norm_num)
  | trans _ _ h _ => exact h

theorem target_mem {Ω : Set ℂ} {x y : ℂ} (p : PlanePolygon Ω x y) : y ∈ Ω := by
  induction p with
  | refl _ h => exact h
  | step a b h => simpa using h 1 (by norm_num)
  | trans _ _ _ h => exact h

noncomputable def pathIn {Ω : Set ℂ} {x y : ℂ} (p : PlanePolygon Ω x y) :
    Path (⟨x,p.source_mem⟩ : Ω) ⟨y,p.target_mem⟩ := by
  induction p with
  | refl a h => exact Path.refl _
  | trans p q ihp ihq => exact ihp.trans ihq
  | step a b h =>
    exact {
      toFun := fun s => ⟨AffineMap.lineMap (k := ℝ) a b (s : ℝ),h s s.property⟩
      continuous_toFun := (AffineMap.lineMap_continuous.comp continuous_subtype_val).subtype_mk _
      source' := Subtype.ext (AffineMap.lineMap_apply_zero _ _)
      target' := Subtype.ext (AffineMap.lineMap_apply_one _ _) }

end PlanePolygon

/-- A finite polygon in the covering plane with identified endpoints.
Its projection is a closed piecewise linear path on the punctured torus. -/
structure TorusPeriodPolygon (L : PeriodPair) where
  start : ℂ
  finish : ℂ
  edges : PlanePolygon (L.lattice : Set ℂ)ᶜ start finish
  closed : finish-start ∈ L.lattice

def TorusPeriodPolygon.base {L : PeriodPair} (γ : TorusPeriodPolygon L) : PuncturedPeriodTorus L :=
  puncturedPlaneProjection L ⟨γ.start,γ.edges.source_mem⟩

noncomputable def TorusPeriodPolygon.loop {L : PeriodPair} (γ : TorusPeriodPolygon L) :
    Path γ.base γ.base := by
  exact (γ.edges.pathIn.map (puncturedPlaneProjection_continuous L)).cast rfl (Subtype.ext ((periodTorusProjection_eq_iff L _ _).mpr γ.closed))

end TwoAxisHelicoid
