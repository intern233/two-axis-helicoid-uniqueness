import TwoAxisHelicoid.OneEndedBallExterior
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Connected.LocallyConnected

namespace TwoAxisHelicoid
open Set Filter Metric Topology InnerProductSpace
open scoped Topology ContDiff Manifold

/-- In a connected locally connected space, each component of an open
set with preconnected complement has preconnected complement as well. -/
theorem complement_open_component_preconnected {M : Type*} [TopologicalSpace M] [PreconnectedSpace M]
    [LocallyConnectedSpace M] {U : Set M} (op : IsOpen U) (outside : IsPreconnected Uᶜ) (p : M) :
    IsPreconnected (connectedComponentIn U p)ᶜ := by
  by_cases hp : p∈U
  · let V := connectedComponentIn U p
    have pv : p∈V := mem_connectedComponentIn hp
    have vsub : V⊆U := connectedComponentIn_subset _ _
    have vo : IsOpen V := op.connectedComponentIn
    have rest : IsOpen (U∩Vᶜ) := by
      apply isOpen_iff_mem_nhds.mpr
      rintro x ⟨xu,xv⟩
      apply mem_of_superset ((op.connectedComponentIn (x := x)).mem_nhds (mem_connectedComponentIn xu))
      intro y hy
      refine ⟨connectedComponentIn_subset U x hy,fun inV => xv ?_⟩
      have eq : connectedComponentIn U x=V := (connectedComponentIn_eq hy).trans (connectedComponentIn_eq inV).symm
      exact eq ▸ mem_connectedComponentIn xu
    intro a b oa ob cov ha hb
    by_contra empty
    have covU : Uᶜ⊆a∪b := (compl_subset_compl.mpr vsub).trans cov
    have reject (A B : Set M) (aO : IsOpen A) (bO : IsOpen B)
        (cover : Vᶜ⊆A∪B) (apart : Disjoint (Vᶜ∩A) B) (non : (Vᶜ∩B).Nonempty)
        (miss : Disjoint Uᶜ B) : False := by
      have inU : Vᶜ∩B⊆U := fun x hx => by
        by_contra nx
        exact disjoint_left.mp miss nx hx.2
      have same : Vᶜ∩B=(U∩Vᶜ)∩B := Subset.antisymm (fun x hx => ⟨⟨inU hx,hx.1⟩,hx.2⟩) (fun _ h => ⟨h.1.2,h.2⟩)
      have openB : IsOpen (Vᶜ∩B) := same ▸ rest.inter bO
      have closedB : IsClosed (Vᶜ∩B) := by
        have e : (Vᶜ∩B)ᶜ=V∪A := by
          ext x
          constructor
          · intro h
            by_cases hx : x∈V
            · exact Or.inl hx
            · exact Or.inr ((cover hx).resolve_right fun bx => h ⟨hx,bx⟩)
          · rintro (hx|ax) ⟨nx,bx⟩
            · exact nx hx
            · exact disjoint_left.mp apart ⟨nx,ax⟩ bx
        exact isOpen_compl_iff.mp (e ▸ vo.union aO)
      have full := (isClopen_iff.mp ⟨closedB,openB⟩).resolve_left non.ne_empty
      exact (show p∈Vᶜ∩B from full ▸ mem_univ p).1 pv
    have dis : Disjoint (Vᶜ∩a) b := disjoint_left.mpr fun x h b' => empty ⟨x,h.1,h.2,b'⟩
    by_cases meet : (Uᶜ∩a).Nonempty
    · apply reject a b oa ob cov dis hb
      apply disjoint_left.mpr
      intro x xu xb
      obtain ⟨y,yu,ya,yb⟩ := outside a b oa ob covU meet ⟨x,xu,xb⟩
      exact empty ⟨y,(compl_subset_compl.mpr vsub) yu,ya,yb⟩
    · exact reject b a ob oa (fun x hx => (cov hx).symm)
        (disjoint_left.mpr fun x h xa => disjoint_left.mp dis ⟨h.1,xa⟩ h.2) ha
        (disjoint_left.mpr fun x xu xa => meet ⟨x,xu,xa⟩)
  · rw [connectedComponentIn_eq_empty hp,compl_empty]
    exact isPreconnected_univ

/-- The weak superlevel is the closure of the strict superlevel when
the function cannot attain a local maximum at a level point. -/
theorem weak_superlevel_closure_of_no_local_max {M : Type*} [TopologicalSpace M] {f : M → ℝ}
    (cf : Continuous f) (r : ℝ) (maximum : ∀ p : M, f p=r → ¬IsLocalMax f p) :
    closure {x | r<f x}={x | r≤f x} := by
  apply Subset.antisymm (closure_minimal (fun x (h : r<f x) => (show r≤f x from h.le)) (isClosed_le continuous_const cf))
  intro x hx
  by_contra outside
  have h : f x=r := le_antisymm (le_of_not_gt fun h => outside (subset_closure h)) hx
  apply maximum x h
  filter_upwards [isClosed_closure.isOpen_compl.mem_nhds outside] with y hy
  rw [h]
  exact le_of_not_gt fun hi => hy (subset_closure hi)

/-- Every component cut out by an open extrinsic ball on a proper
one-ended harmonic immersion has a preconnected complement in the
parameter surface. There is no transversality requirement on the ball. -/
theorem one_ended_harmonic_ball_component_complement {M E : Type*}
    [TopologicalSpace M] [T2Space M] [PreconnectedSpace M] [LocallyConnectedSpace M] [ChartedSpace ℂ M]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
    (tails : HasConnectedCompactTails M) {X : M → E} (proper : IsProperMap X)
    (reg : ∀ p : M, let e := chartAt ℂ p
      HarmonicAt (X ∘ e.symm) (e p) ∧ Function.Injective (fderiv ℝ (X ∘ e.symm) (e p))) (c : E) (r : ℝ) (p : M) :
    IsPreconnected (connectedComponentIn (X ⁻¹' ball c r) p)ᶜ := by
  apply complement_open_component_preconnected (isOpen_ball.preimage proper.continuous)
  have closed : (X ⁻¹' ball c r)ᶜ={x | r≤dist (X x) c} := by
    ext x
    change (¬dist (X x) c<r) ↔ r≤dist (X x) c
    exact not_lt
  rw [closed,← weak_superlevel_closure_of_no_local_max (proper.continuous.dist continuous_const) r]
  · exact (one_ended_harmonic_immersion_ball_exterior tails proper reg c r).closure
  · intro x _ max
    let e := chartAt ℂ x
    have eq : e.symm (e x)=x := e.left_inv (mem_chart_source ℂ x)
    have lim : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
      simpa only [eq] using (e.symm.continuousAt (e.map_source (mem_chart_source ℂ x))).tendsto
    apply harmonic_immersion_no_local_distance_max (reg x).1 (reg x).2 c
    have ev : ∀ᶠ z in 𝓝 (e x), dist (X (e.symm z)) c≤dist (X x) c := lim.eventually max
    change ∀ᶠ w in 𝓝 (e x), dist (X (e.symm w)) c≤dist (X (e.symm (e x))) c
    rwa [eq]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.one_ended_harmonic_ball_component_complement
#print axioms TwoAxisHelicoid.complement_open_component_preconnected
#print axioms TwoAxisHelicoid.weak_superlevel_closure_of_no_local_max
