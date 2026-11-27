import TwoAxisHelicoid.CompactMinimalBallHull
import TwoAxisHelicoid.ExteriorHeightEscape
import TwoAxisHelicoid.PuncturedTorusRealOrientation

namespace TwoAxisHelicoid
open Complex Set Filter Metric Topology InnerProductSpace
open scoped Topology ContDiff Manifold

/-- A compact set with the boundary maximum principle cannot enclose a
bounded component of a strict superlevel set. On a one-ended space the
remaining component accounts for the entire superlevel. -/
theorem one_ended_superlevel_preconnected {M : Type*} [TopologicalSpace M] [T2Space M]
    (tails : HasConnectedCompactTails M) {f : M → ℝ} (continuous : Continuous f) (r : ℝ)
    (sublevel : IsCompact {x | f x≤r})
    (maximum : ∀ K : Set M, IsCompact K → (∀ x∈frontier K, f x≤r) → ∀ x∈K, f x≤r) :
    IsPreconnected {x | r<f x} := by
  let U := {x | r<f x}
  have op : IsOpen U := isOpen_lt continuous_const continuous
  obtain ⟨T,connected,compact,away⟩ := tails _ sublevel
  have inside : T ⊆ U := by
    intro x hx
    change r<f x
    exact lt_of_not_ge (fun h => disjoint_left.mp away hx (show x∈{y | f y≤r} from h))
  intro a b oa ob cover ha hb
  by_contra dis
  have impossible (V W : Set M) (ov : IsOpen V) (ow : IsOpen W)
      (cover' : U ⊆ V ∪ W) (apart : Disjoint V W)
      (below : V ⊆ U) (non : V.Nonempty) (empty : Disjoint V T) : False := by
    have inCore : closure V ⊆ Tᶜ := closure_minimal (disjoint_left.mp empty) compact.isClosed
    have K := compact.of_isClosed_subset isClosed_closure inCore
    have noW : closure V ⊆ Wᶜ := closure_minimal (disjoint_left.mp apart) ow.isClosed_compl
    have bound : ∀ x∈frontier (closure V), f x≤r := by
      intro x hx
      by_contra! hi
      have edge : x∈frontier V := frontier_closure_subset hx
      rcases cover' (show x∈U from hi) with h|h
      · exact edge.2 (ov.interior_eq.symm ▸ h)
      · exact noW edge.1 h
    obtain ⟨x,hx⟩ := non
    exact (not_lt_of_ge (maximum _ K bound x (subset_closure hx))) (below hx)
  have cover' : U ⊆ (U∩a) ∪ (U∩b) := fun x hx => (cover hx).elim (fun h => Or.inl ⟨hx,h⟩) (fun h => Or.inr ⟨hx,h⟩)
  have apart : Disjoint (U∩a) (U∩b) := disjoint_left.mpr fun x hx hy => dis ⟨x,hx.1,hx.2,hy.2⟩
  by_cases meets : (T∩a).Nonempty
  · have empty : Disjoint (U∩b) T := disjoint_left.mpr (fun x hx ht => by
      obtain ⟨y,hy,ya,yb⟩ := connected a b oa ob (inside.trans cover) meets ⟨x,ht,hx.2⟩
      exact dis ⟨y,inside hy,ya,yb⟩)
    exact impossible _ _ (op.inter ob) (op.inter oa) (fun x hx => (cover' hx).symm) apart.symm inter_subset_left hb empty
  · exact impossible _ _ (op.inter oa) (op.inter ob) cover' apart inter_subset_left ha
      (disjoint_left.mpr fun x hx ht => meets ⟨x,ht,hx.2⟩)

/-- The exterior of every Euclidean ball on a proper one-ended harmonic
immersion is preconnected. The radius may be a critical value. -/
theorem one_ended_harmonic_immersion_ball_exterior {M E : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
    (tails : HasConnectedCompactTails M) {X : M → E} (proper : IsProperMap X)
    (reg : ∀ p : M, let e := chartAt ℂ p
      HarmonicAt (X ∘ e.symm) (e p) ∧ Function.Injective (fderiv ℝ (X ∘ e.symm) (e p))) (c : E) (r : ℝ) :
    IsPreconnected {x | r<dist (X x) c} := by
  apply one_ended_superlevel_preconnected tails (proper.continuous.dist continuous_const) r
  · exact proper.isCompact_preimage (isCompact_closedBall c r)
  · intro K hK edge x hx
    exact compact_harmonic_patch_ball_hull proper.continuous reg hK (fun z hz => edge z hz) hx

/-- Applied to the original smooth minimal surface in Euclidean space.
Neither its asymptotic description nor embeddedness of any particular
piece of a ball is needed for this conclusion. -/
theorem OriginalSmoothHelicoid.ball_exterior_preconnected (s : OriginalSmoothHelicoid)
    (c : EuclideanSpace ℝ (Fin 3)) (r : ℝ) : IsPreconnected {x | r<dist (s.euclideanPosition x) c} := by
  obtain ⟨S,_,charts⟩ := punctured_torus_minimal_induced_harmonic_atlas s.topologicalType s.smooth s.immersion s.minimal
  let _ := S
  apply one_ended_harmonic_immersion_ball_exterior (homeomorphic_punctured_surface_connected_tails (0:PeriodTorus s.modelTorus) s.topologicalType) s.euclidean_proper
  intro x
  let e := chartAt ℂ x
  obtain ⟨hh,_,hi⟩ := charts e (chart_mem_atlas ℂ x) (e x) (e.map_source (mem_chart_source ℂ x))
  have har := spatial_harmonic_of_coordinates hh
  refine ⟨har.comp_CLM coordinateToEuclidean,?_⟩
  change Function.Injective (fderiv ℝ (coordinateToEuclidean ∘ (s.position ∘ e.symm)) (e x))
  have d := coordinateToEuclidean.hasFDerivAt.comp (e x) (har.1.differentiableAt two_ne_zero).hasFDerivAt
  change Function.Injective (fderiv ℝ (coordinateToEuclidean ∘ fun w => s.position (e.symm w)) (e x))
  rw [d.fderiv]
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.injective.comp hi

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.OriginalSmoothHelicoid.ball_exterior_preconnected
#print axioms TwoAxisHelicoid.one_ended_superlevel_preconnected
#print axioms TwoAxisHelicoid.one_ended_harmonic_immersion_ball_exterior
