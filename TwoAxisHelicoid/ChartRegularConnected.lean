import TwoAxisHelicoid.ChartFinitePoles
import TwoAxisHelicoid.AvoidingPathGeometry

namespace TwoAxisHelicoid
open Set

namespace HolomorphicCoefficientDisks
variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [PreconnectedSpace X]

/-- Any two regular points can be joined by an actual piecewise coordinate
linear path avoiding a prescribed finite set. -/
theorem exists_avoiding_finite_path (A : HolomorphicCoefficientDisks X)
    {P : Set X} (hP : P.Finite) {x y : X} (hx : x ∉ P) (hy : y ∉ P) :
    Nonempty (A.AvoidingPath Pᶜ x y) := by
  obtain ⟨r,hr⟩ := A.primitives.exists_chain x y
  obtain ⟨V,W,_hV,_hW,hxV,hyW,h⟩ := hr.regular_approximation
    (finite_compl_dense_complex_charts hP) 1 (by norm_num)
  obtain ⟨s,hs,_he⟩ := h x hxV y hyW hx hy
  obtain ⟨c,_hc⟩ := regular_chain_lifts_to_avoiding_path hP hs
  exact ⟨c⟩

theorem regular_points_joined (A : HolomorphicCoefficientDisks X)
    {P : Set X} (hP : P.Finite) {x y : X} (hx : x ∉ P) (hy : y ∉ P) :
    JoinedIn Pᶜ x y := by
  obtain ⟨c⟩ := A.exists_avoiding_finite_path hP hx hy
  exact ⟨c.path,fun s => c.range_subset ⟨s,rfl⟩⟩

end HolomorphicCoefficientDisks
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.HolomorphicCoefficientDisks.regular_points_joined
