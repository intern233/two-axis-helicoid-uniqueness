import TwoAxisHelicoid.ChartAvoidingPaths

namespace TwoAxisHelicoid
open Set
open scoped unitInterval

namespace HolomorphicCoefficientDisks
variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

theorem segmentPath_coordinates (A : HolomorphicCoefficientDisks X) (p : X) {x y : X}
    (hx : x ∈ A.primitives.domain p) (hy : y ∈ A.primitives.domain p) (s : unitInterval) :
    (chartAt ℂ p) (A.segmentPath p hx hy s) = chartSegment p x y s := by
  change (chartAt ℂ p) ((chartAt ℂ p).symm (chartSegment p x y s)) = _
  exact (chartAt ℂ p).right_inv (A.ball_target p (A.chartSegment_mem p hx hy s.property))

theorem AvoidingPath.range_subset {A : HolomorphicCoefficientDisks X} {U : Set X}
    {x y : X} (c : A.AvoidingPath U x y) : range c.path ⊆ U := by
  induction c with
  | refl x hx =>
      rintro _ ⟨s,rfl⟩
      exact hx
  | step p x y hx hy hU =>
      rintro _ ⟨s,rfl⟩
      exact hU s s.property
  | trans c d hc hd =>
      change range (c.path.trans d.path) ⊆ U
      rw [Path.trans_range]
      exact union_subset hc hd

end HolomorphicCoefficientDisks
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.HolomorphicCoefficientDisks.AvoidingPath.range_subset
