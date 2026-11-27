import TwoAxisHelicoid.FinitePlaneWinding

namespace TwoAxisHelicoid
open Complex Set Filter Topology Metric
open scoped Topology

/-- A continuous plane map with finite fibers and outer winding one
has precisely one simple preimage of each value if all local degrees
have a common sign and strictly positive absolute multiplicity. -/
theorem degree_one_plane_fibers {F : ℂ → ℂ} (cont : Continuous F)
    (finite : ∀ c, (F ⁻¹' {c}).Finite) {s : ℤ} (sign : s=1 ∨ s= -1)
    (k : ℂ → ℕ) (localDegree : ∀ p, HasPlaneOrientationAt F p (((k p+1:ℕ):ℤ)*s))
    (outer : ∀ c : ℂ, ∀ᶠ r : ℝ in atTop,
      HasOrientationCircleDegree (fun a => planeOrientationDirection (F (r • orientationRay a)-c)) 1) :
    (∀ c, ∃! z, F z=c) ∧ s=1 ∧ ∀ z, k z=0 := by
  classical
  have fiber (c : ℂ) : (∃! z, F z=c) ∧ s=1 ∧ ∀ z, F z=c → k z=0 := by
    let S := (finite c).toFinset
    have mem (z : ℂ) : z∈S ↔ F z=c := (finite c).mem_toFinset
    obtain ⟨B,bound⟩ := (finite c).isBounded.exists_norm_le
    obtain ⟨r,deg,above,rp⟩ := ((outer c).and ((eventually_gt_atTop B).and (eventually_gt_atTop 0))).exists
    let angle := fun z => planeOrientationDirection (F z-c)
    have regular : ContinuousOn angle (S : Set ℂ)ᶜ := by
      intro z hz
      have ne : F z≠c := fun e => hz ((mem z).mpr e)
      exact ((planeOrientationDirection_continuousAt (sub_ne_zero.mpr ne)).comp (f := fun w => F w-c) (cont.continuousAt.sub continuousAt_const)).continuousWithinAt
    have wd (z : ℂ) (hz : z∈S) : HasLocalWinding angle z (((k z+1:ℕ):ℤ)*s) := by
      have eq := (mem z).mp hz
      obtain ⟨T,tp,h⟩ := localDegree z
      refine ⟨T,tp,fun r hr => ?_⟩
      have degree := h r hr
      change HasOrientationCircleDegree (fun a => planeOrientationDirection (F (z+r • orientationRay a)-F z)) _ at degree
      rw [eq] at degree
      exact degree
    have summed := winding_sum_of_finite_plane_singularities S angle _ regular wd rp
      (fun z hz => (bound z ((mem z).mp hz)).trans_lt above)
    have sum : (∑ z∈S, ((k z+1:ℕ):ℤ))*s=1 := by
      rw [Finset.sum_mul]
      exact summed.unique deg
    have nonneg : (0:ℤ)≤∑ z∈S, ((k z+1:ℕ):ℤ) := Finset.sum_nonneg (fun _ _ => by positivity)
    have positive : s=1 := sign.resolve_right fun neg => by rw [neg,mul_neg_one] at sum; omega
    rw [positive,mul_one] at sum
    have simple (z : ℂ) (hz : z∈S) : k z=0 := by
      have bound := Finset.single_le_sum (f := fun z => ((k z+1:ℕ):ℤ)) (fun _ _ => by positivity) hz
      rw [sum] at bound
      omega
    have ones : (∑ z∈S, ((k z+1:ℕ):ℤ))=∑ _z∈S, (1:ℤ) := by
      apply Finset.sum_congr rfl
      intro z hz
      simp [simple z hz]
    rw [ones] at sum
    have card : S.card=1 := by simpa using sum
    obtain ⟨z,hz⟩ := Finset.card_eq_one.mp card
    refine ⟨⟨z,(mem z).mp (by rw [hz]; exact Finset.mem_singleton_self _),?_⟩,positive,
      fun y hy => simple y ((mem y).mpr hy)⟩
    intro y hy
    have hy' := (mem y).mpr hy
    rwa [hz,Finset.mem_singleton] at hy'
  exact ⟨fun c => (fiber c).1,(fiber 0).2.1,fun z => (fiber (F z)).2.2 z rfl⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.degree_one_plane_fibers
