import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Order.Preorder.Finite
import Mathlib.Topology.Instances.Real.Lemmas

namespace TwoAxisHelicoid

theorem continuous_distinct_real_order {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g) (hne : ∀ x, f x ≠ g x)
    {a b : X} (ha : f a < g a) : f b < g b := by
  by_contra hb
  obtain ⟨x,hx⟩ := intermediate_value_univ₂ hf hg ha.le (le_of_not_gt hb)
  exact hne x hx

/-- Continuously moving, pairwise distinct real heights preserve their
strict ordering. This is the no-crossing step for sheets of a normal cover. -/
theorem continuous_heights_preserve_order {X I : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] [LinearOrder I] {h : I → X → ℝ}
    (hc : ∀ i, Continuous (h i)) (hi : ∀ x, Function.Injective (fun i => h i x))
    {a : X} (ha : StrictMono (fun i => h i a)) (b : X) :
    StrictMono (fun i => h i b) := by
  intro i j hij
  apply continuous_distinct_real_order (hc i) (hc j) _ (ha hij)
  intro x he
  exact hij.ne (hi x he)

/-- A return map of a finite ordered collection of lifted heights is the
identity. The conclusion is proved from continuity and absence of crossings;
order preservation is not assumed as an extra monodromy hypothesis. -/
theorem finite_ordered_height_monodromy_identity {X I : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] [LinearOrder I] [Finite I] {h : I → X → ℝ}
    (hc : ∀ i, Continuous (h i)) (hi : ∀ x, Function.Injective (fun i => h i x))
    {a b : X} (ha : StrictMono (fun i => h i a)) (σ : I → I)
    (hreturn : ∀ i, h i b = h (σ i) a) : σ = id := by
  apply StrictMono.eq_id
  intro i j hij
  apply ha.lt_iff_lt.mp
  rw [← hreturn i,← hreturn j]
  exact continuous_heights_preserve_order hc hi ha b hij

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.finite_ordered_height_monodromy_identity
