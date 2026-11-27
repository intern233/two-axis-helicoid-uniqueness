import TwoAxisHelicoid.HarmonicLocalMaximum
import TwoAxisHelicoid.AmbientHarmonicImmersion
import TwoAxisHelicoid.OriginalHelicoidRepresentative

namespace TwoAxisHelicoid
open Complex Set Filter Metric Topology InnerProductSpace
open scoped Topology ContDiff Manifold InnerProductSpace

/-- A regular harmonic immersion cannot attain an interior local maximum
of its Euclidean distance to any fixed center. At a supporting sphere,
the affine tangent functional attains a harmonic local maximum. -/
theorem harmonic_immersion_no_local_distance_max {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : ℂ → E} {z : ℂ} (harmonic : HarmonicAt X z) (immersion : Function.Injective (fderiv ℝ X z))
    (c : E) : ¬IsLocalMax (fun w => dist (X w) c) z := by
  intro maximum
  let u := X z-c
  let Y := fun w => X w-c
  have scoreH : HarmonicAt (fun w => ⟪u,Y w⟫_ℝ) z :=
    (harmonic.sub (harmonicAt_const c)).comp_CLM (innerSL ℝ u)
  have sm : IsLocalMax (fun w => ⟪u,Y w⟫_ℝ) z := by
    filter_upwards [maximum] with w h
    rw [dist_eq_norm,dist_eq_norm] at h
    change ‖Y w‖≤‖u‖ at h
    change ⟪u,Y w⟫_ℝ≤⟪u,u⟫_ℝ
    rw [real_inner_self_eq_norm_sq,pow_two]
    exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left h (norm_nonneg _))
  have score := harmonic_eventually_constant_at_local_max scoreH sm
  have eq : X=ᶠ[𝓝 z] fun _ => X z := by
    filter_upwards [maximum,score] with w h l
    rw [dist_eq_norm,dist_eq_norm] at h
    change ‖Y w‖≤‖u‖ at h
    change ⟪u,Y w⟫_ℝ=⟪u,u⟫_ℝ at l
    rw [real_inner_self_eq_norm_sq] at l
    have e : u-Y w=0 := by
      apply norm_eq_zero.mp
      have form := norm_sub_sq_real u (Y w)
      rw [l] at form
      nlinarith [sq_le_sq' (by linarith [norm_nonneg (Y w),norm_nonneg u] : -‖u‖≤‖Y w‖) h,sq_nonneg ‖u-Y w‖]
    exact sub_left_inj.mp (show X w-c=X z-c from (sub_eq_zero.mp e).symm)
  have zero : fderiv ℝ X z=0 := eq.fderiv_eq.trans (fderiv_const_apply _)
  exact one_ne_zero (immersion (show (fderiv ℝ X z) 1=(fderiv ℝ X z) 0 by rw [zero]; rfl))

/-- If the entire boundary of a compact portion lies in a Euclidean
closed ball, the same bound holds throughout the portion. The portion
may be disconnected and its boundary need not be regular. -/
theorem compact_harmonic_patch_ball_hull {M E : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {X : M → E} (continuous : Continuous X)
    (reg : ∀ p : M, let e := chartAt ℂ p
      HarmonicAt (X ∘ e.symm) (e p) ∧ Function.Injective (fderiv ℝ (X ∘ e.symm) (e p)))
    {K : Set M} (compact : IsCompact K) {c : E} {r : ℝ}
    (boundary : MapsTo X (frontier K) (closedBall c r)) : MapsTo X K (closedBall c r) := by
  intro x hx
  obtain ⟨p,hp,maximum⟩ := compact.exists_isMaxOn ⟨x,hx⟩ (continuous.dist continuous_const).continuousOn
  by_cases edge : p∈frontier K
  · exact (show dist (X x) c≤dist (X p) c from maximum hx).trans (mem_closedBall.mp (boundary edge))
  · have inside : p∈interior K := by
      by_contra h
      exact edge ⟨subset_closure hp,h⟩
    let e := chartAt ℂ p
    have atP : e.symm (e p)=p := e.left_inv (mem_chart_source ℂ p)
    have near : ∀ᶠ w in 𝓝 (e p), e.symm w∈K := by
      have lim : Tendsto e.symm (𝓝 (e p)) (𝓝 p) := by simpa only [atP] using (e.symm.continuousAt (e.map_source (mem_chart_source ℂ p))).tendsto
      exact lim.eventually (mem_interior_iff_mem_nhds.mp inside)
    have closed : IsLocalMax (fun w => dist ((X ∘ e.symm) w) c) (e p) := by
      filter_upwards [near] with z hz
      simpa only [Function.comp_apply,atP] using (show dist (X (e.symm z)) c≤dist (X p) c from maximum hz)
    exact (harmonic_immersion_no_local_distance_max (reg p).1 (reg p).2 c closed).elim

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_immersion_no_local_distance_max
#print axioms TwoAxisHelicoid.compact_harmonic_patch_ball_hull
