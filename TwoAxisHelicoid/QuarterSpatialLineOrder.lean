import TwoAxisHelicoid.QuarterSpatialPathBounds

namespace TwoAxisHelicoid
open Complex Set

/-- A checked uniform upper or lower bound on the spatial rate gives
the corresponding order on every point of that physical line. -/
theorem CheckedQuarterSpatialLine.primitive_order {f v e l r a b L U}
    (cert : CheckedQuarterSpatialLine f v v e l r a b L U) :
    let p := certifiedClosedParameters
    ∀ {X : ℂ → Fin 3 → ℝ}, HasTwoAxisHelicoidCoordinateDifferential X p.t p.a 1 p.height_pos →
      (∀ x∈Icc (l:ℝ) r, centralBandEdgePoint v e x∉certifiedPeriodPair.lattice) →
      let g := fun x : ℝ => X (centralBandEdgePoint v e x) (if f then 0 else 1)
      (b≤0 → AntitoneOn g (Icc (l:ℝ) r)) ∧ (0≤a → MonotoneOn g (Icc (l:ℝ) r)) := by
  intro p X d off g
  have df {x : ℝ} (hx : x∈Icc (l:ℝ) r) :
      HasDerivAt g (quarterSpatialRate f v (centralBandEdgePoint v e x)) x :=
    quarter_spatial_line_hasDerivAt f v e x d (off x hx)
  have c : ContinuousOn g (Icc (l:ℝ) r) := fun x hx => (df hx).continuousAt.continuousWithinAt
  constructor
  · intro upper
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) c (fun _ hx => (df (interior_subset hx)).differentiableAt.differentiableWithinAt)
    intro x hx
    have inJ := interior_subset hx
    rw [(df inJ).deriv]
    exact (cert.sound.1 x inJ).2.trans (by exact_mod_cast upper)
  · intro lower
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) c (fun _ hx => (df (interior_subset hx)).differentiableAt.differentiableWithinAt)
    intro x hx
    have inJ := interior_subset hx
    rw [(df inJ).deriv]
    exact (by exact_mod_cast lower : (0:ℝ)≤a).trans (cert.sound.1 x inJ).1

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.CheckedQuarterSpatialLine.primitive_order
