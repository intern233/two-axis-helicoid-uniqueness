import TwoAxisHelicoid.CompactFamilyPhaseObstruction
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.UnitInterval

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology unitInterval

/-- Lifts of one continuous path in the marked torus differ by a
constant lattice period and have the same displacement. -/
theorem lifted_paths_equal_displacement (L : PeriodPair) (a b : C(I,ℂ))
    (same : ∀ t, periodTorusProjection L (a t)=periodTorusProjection L (b t)) :
    a 1-a 0=b 1-b 0 := by
  let diff := fun t : I => a t-b t
  have discrete : IsDiscrete (L.lattice : Set ℂ) :=
    isDiscrete_iff_discreteTopology.mpr (inferInstanceAs (DiscreteTopology L.lattice))
  have lattice : MapsTo diff univ (L.lattice : Set ℂ) :=
    fun t _ => (periodTorusProjection_eq_iff L (b t) (a t)).mp (same t).symm
  have constant := isPreconnected_univ.constant_of_mapsTo discrete (a.continuous.sub b.continuous).continuousOn lattice
    (mem_univ (1:I)) (mem_univ (0:I))
  change a 1-b 1=a 0-b 0 at constant
  linear_combination constant

/-- Continuous real lifts of the two marked phases give a lift of the
map to the actual covering plane in the prescribed period basis. -/
theorem plane_lift_of_two_marked_angles {X : Type*} [TopologicalSpace X] (L : PeriodPair)
    (H : PeriodTorus L ≃ₜ Circle×Circle) (marked : ∀ z, H (periodTorusProjection L z)=planeCircleCoordinates L z)
    (f : X → PeriodTorus L) (a b : C(X,ℝ)) (angles : ∀ x, normalizedPhase (a x)=(H (f x)).1 ∧
      normalizedPhase (b x)=(H (f x)).2) :
    ∃ z : C(X,ℂ), ∀ x, periodTorusProjection L (z x)=f x := by
  let z := fun x => spinSquareLinear L (a x) (b x)
  have cz : Continuous z := (a.continuous.smul continuous_const).add (b.continuous.smul continuous_const)
  refine ⟨⟨z,cz⟩,?_⟩
  intro x
  apply H.injective
  rw [marked]
  obtain ⟨u,v⟩ := spinSquareLinear_coords L (a x) (b x)
  change (normalizedPhase (L.basis.repr (z x) 0),normalizedPhase (L.basis.repr (z x) 1))=H (f x)
  dsimp only [z]
  rw [u,v]
  exact Prod.ext (angles x).1 (angles x).2

/-- Two continuously moving arcs share both physical endpoints at each
height. If their plane lifts have different displacements at the base
height then nearby actual height components have a marked obstruction.
The compact connected parameter space is the union of their ranges
in the continuous function space of the deformation parameter. -/
theorem nearby_obstructed_height_from_paired_paths {S : Type*} [TopologicalSpace S] [LocallyCompactSpace S]
    (L : PeriodPair) (H : PeriodTorus L ≃ₜ Circle×Circle)
    (marked : ∀ z, H (periodTorusProjection L z)=planeCircleCoordinates L z)
    (P Q : C(S×I,PeriodTorus L)) {h : PeriodTorus L → ℝ} {v : S → ℝ}
    (levels : ∀ s t, h (P (s,t))=v s ∧ h (Q (s,t))=v s)
    (first : ∀ s, P (s,0)=Q (s,0)) (last : ∀ s, P (s,1)=Q (s,1))
    (s₀ : S) (A B : C(I,ℂ)) (liftA : ∀ t, periodTorusProjection L (A t)=P (s₀,t))
    (liftB : ∀ t, periodTorusProjection L (B t)=Q (s₀,t))
    (different : A 1-A 0≠B 1-B 0) :
    ∀ᶠ s in 𝓝 s₀, ∃ x : h ⁻¹' {v s}, ¬∃ a b : C(connectedComponent x,ℝ), ∀ q : connectedComponent x,
      normalizedPhase (a q)=(H q.1.1).1 ∧ normalizedPhase (b q)=(H q.1.1).2 := by
  let swap : C(I×S,S×I) := ⟨Prod.swap,continuous_swap⟩
  let U := (P.comp swap).curry
  let V := (Q.comp swap).curry
  let T := range U ∪ range V
  let : CompactSpace T := isCompact_iff_compactSpace.mp ((isCompact_range U.continuous).union (isCompact_range V.continuous))
  have start : U 0=V 0 := ContinuousMap.ext first
  have finish : U 1=V 1 := ContinuousMap.ext last
  let : PreconnectedSpace T := isPreconnected_iff_preconnectedSpace.mp
    (IsPreconnected.union' ⟨U 0,mem_range_self _,⟨0,start.symm⟩⟩ (isPreconnected_range U.continuous) (isPreconnected_range V.continuous))
  let l : C(I,T) := ⟨fun t => ⟨U t,Or.inl (mem_range_self t)⟩,U.continuous.subtype_mk _⟩
  let r : C(I,T) := ⟨fun t => ⟨V t,Or.inr (mem_range_self t)⟩,V.continuous.subtype_mk _⟩
  let E : C(S×T,PeriodTorus L) := ⟨fun q => q.2.1 q.1,(continuous_subtype_val.comp continuous_snd).eval continuous_fst⟩
  have heights (s : S) (q : T) : h (E (s,q))=v s := by
    rcases q with ⟨q,⟨t,rfl⟩|⟨t,rfl⟩⟩
    · exact (levels s t).1
    · exact (levels s t).2
  apply nearby_height_component_nonlifting E ⟨H,H.continuous⟩ heights s₀ (l 0)
  rintro ⟨u,w,angles⟩
  obtain ⟨Z,projects⟩ := plane_lift_of_two_marked_angles L H marked (fun q => E (s₀,q)) u w angles
  have left := lifted_paths_equal_displacement L (Z.comp l) A (fun t => (projects (l t)).trans (liftA t).symm)
  have right := lifted_paths_equal_displacement L (Z.comp r) B (fun t => (projects (r t)).trans (liftB t).symm)
  change Z (l 1)-Z (l 0)=A 1-A 0 at left
  change Z (r 1)-Z (r 0)=B 1-B 0 at right
  rw [show l 0=r 0 from Subtype.ext start,show l 1=r 1 from Subtype.ext finish] at left
  exact different (left.symm.trans right)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.lifted_paths_equal_displacement
#print axioms TwoAxisHelicoid.nearby_obstructed_height_from_paired_paths
