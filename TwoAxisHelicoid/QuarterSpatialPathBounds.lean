import TwoAxisHelicoid.QuarterSpatialLineSound
import TwoAxisHelicoid.RealPrimitivePeriods

namespace TwoAxisHelicoid
open Complex Set

/-- The rate used by the numerical line certificates is the derivative
of the actual spatial coordinate, on both vertical and horizontal
parameter lines. -/
theorem quarter_spatial_line_hasDerivAt (first v : Bool) (e x : ℝ) :
    let p := certifiedClosedParameters
    ∀ {X : ℂ → Fin 3 → ℝ}, HasTwoAxisHelicoidCoordinateDifferential X p.t p.a 1 p.height_pos →
      centralBandEdgePoint v e x∉certifiedPeriodPair.lattice →
      HasDerivAt (fun u : ℝ => X (centralBandEdgePoint v e u) (if first then 0 else 1))
        (quarterSpatialRate first v (centralBandEdgePoint v e x)) x := by
  intro p X d off
  let Z := centralBandEdgePoint v e
  let j : Fin 3 := if first then 0 else 1
  let velocity := if v then I else 1
  have line : HasDerivAt Z velocity x := by
    cases v
    · have eq : centralBandEdgePoint false e=fun s : ℝ => (s:ℂ)+I*e := by funext s; apply Complex.ext <;> simp [centralBandEdgePoint]
      change HasDerivAt (centralBandEdgePoint false e) 1 x
      rw [eq]
      exact (hasDerivAt_id x).ofReal_comp.add_const _
    · have eq : centralBandEdgePoint true e=fun s : ℝ => (e:ℂ)+I*s := by funext s; apply Complex.ext <;> simp [centralBandEdgePoint]
      change HasDerivAt (centralBandEdgePoint true e) I x
      rw [eq]
      simpa using ((hasDerivAt_id x).ofReal_comp.const_mul I).const_add (e:ℂ)
  exact (actual_coordinate_primitive_component p.height_pos d off j).comp_hasDerivAt x line

theorem CheckedQuarterSpatialLine.primitive_displacement {f v e l r a b L U}
    (cert : CheckedQuarterSpatialLine f v v e l r a b L U) :
    let p := certifiedClosedParameters
    ∀ {X : ℂ → Fin 3 → ℝ}, HasTwoAxisHelicoidCoordinateDifferential X p.t p.a 1 p.height_pos →
      (∀ x∈Icc (l:ℝ) r, centralBandEdgePoint v e x∉certifiedPeriodPair.lattice) →
      X (centralBandEdgePoint v e r) (if f then 0 else 1)-
        X (centralBandEdgePoint v e l) (if f then 0 else 1)∈Icc (L:ℝ) U := by
  intro p X d off
  exact cert.sound.2 _ (fun x hx => quarter_spatial_line_hasDerivAt f v e x d (off x hx))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.quarter_spatial_line_hasDerivAt
#print axioms TwoAxisHelicoid.CheckedQuarterSpatialLine.primitive_displacement
