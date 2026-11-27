import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Set Topology

/-- A rational number in a single Cartesian coordinate strictly
separates the images of two parameter sets. -/
def RationalCoordinateCut {M : Type*} (F : M → Fin 3 → ℝ) (U V : Set M) : Prop :=
  ∃ (j : Fin 3) (r : ℚ), (∀ x∈U, F x j<(r:ℝ)) ∧ ∀ y∈V, (r:ℝ)<F y j

/-- One product patch tests either local injectivity on a common
neighborhood or separation by a rational Cartesian coordinate plane. -/
structure CoordinatePairPatch {M : Type*} [TopologicalSpace M] (F : M → Fin 3 → ℝ) where
  left : Set M
  right : Set M
  open_left : IsOpen left
  open_right : IsOpen right
  separates : InjOn F (left∪right) ∨ RationalCoordinateCut F left right ∨ RationalCoordinateCut F right left

def HasFiniteSpatialSeparationCover {M : Type*} [TopologicalSpace M] (F : M → Fin 3 → ℝ) (K : Set M) : Prop :=
  ∃ P : Finset (CoordinatePairPatch F), ∀ x∈K, ∀ y∈K, ∃ p∈P, x∈p.left ∧ y∈p.right

theorem finite_separation_cover_injective {M : Type*} [TopologicalSpace M] {F : M → Fin 3 → ℝ} {K : Set M}
    (cover : HasFiniteSpatialSeparationCover F K) : InjOn F K := by
  obtain ⟨P,cover⟩ := cover
  intro x hx y hy eq
  obtain ⟨p,_,px,py⟩ := cover x hx y hy
  rcases p.separates with hi|⟨j,r,left,right⟩|⟨j,r,right,left⟩
  · exact hi (Or.inl px) (Or.inr py) eq
  · exact ((left x px).not_ge (eq.symm ▸ (right y py).le)).elim
  · exact ((right y py).not_ge (eq ▸ (left x px).le)).elim

theorem compact_injective_iff_finite_separation_cover {M : Type*} [TopologicalSpace M] {F : M → Fin 3 → ℝ}
    (cont : ∀ j, Continuous fun x => F x j) (loc : ∀ x : M, ∃ U : Set M, IsOpen U ∧ x∈U ∧ InjOn F U)
    {K : Set M} (compact : IsCompact K) : InjOn F K ↔ HasFiniteSpatialSeparationCover F K := by
  classical
  refine ⟨fun hi => ?_,finite_separation_cover_injective⟩
  have cut (a b : M) (j : Fin 3) (h : F a j<F b j) :
      ∃ U V : Set M, IsOpen U ∧ IsOpen V ∧ a∈U ∧ b∈V ∧ RationalCoordinateCut F U V := by
    obtain ⟨r,ra,rb⟩ := exists_rat_btwn h
    exact ⟨{x | F x j<(r:ℝ)},{x | (r:ℝ)<F x j},isOpen_lt (cont _) continuous_const,
      isOpen_lt continuous_const (cont _),ra,rb,j,r,fun _ hx => hx,fun _ hx => hx⟩
  have all : K ×ˢ K ⊆ ⋃ p : CoordinatePairPatch F, p.left ×ˢ p.right := by
    rintro ⟨x,y⟩ ⟨hx,hy⟩
    by_cases same : F x=F y
    · have xy : x=y := hi (x₁ := x) (x₂ := y) hx hy same
      subst y
      obtain ⟨U,op,xu,inj⟩ := loc x
      exact mem_iUnion.mpr ⟨⟨U,U,op,op,Or.inl (by simpa only [union_self] using inj)⟩,xu,xu⟩
    · have diff : ∃ j, F x j≠F y j := by by_contra! h; exact same (funext h)
      obtain ⟨j,d⟩ := diff
      rcases lt_or_gt_of_ne d with h|h
      · obtain ⟨U,V,uo,vo,xu,yv,c⟩ := cut x y j h
        exact mem_iUnion.mpr ⟨⟨U,V,uo,vo,Or.inr (Or.inl c)⟩,xu,yv⟩
      · obtain ⟨V,U,vo,uo,yv,xu,c⟩ := cut y x j h
        exact mem_iUnion.mpr ⟨⟨U,V,uo,vo,Or.inr (Or.inr c)⟩,xu,yv⟩
  obtain ⟨P,sub⟩ := (compact.prod compact).elim_finite_subcover (fun p : CoordinatePairPatch F => p.left ×ˢ p.right)
    (fun p => p.open_left.prod p.open_right) all
  refine ⟨P,?_⟩
  intro x hx y hy
  obtain ⟨p,h⟩ := mem_iUnion.mp (sub (show (x,y)∈K ×ˢ K from ⟨hx,hy⟩))
  obtain ⟨hp,pair⟩ := mem_iUnion.mp h
  exact ⟨p,hp,pair.1,pair.2⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_injective_iff_finite_separation_cover
#print axioms TwoAxisHelicoid.finite_separation_cover_injective
