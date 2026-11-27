import TwoAxisHelicoid.CompactCoreUnmarkedLifts
import TwoAxisHelicoid.MovingReflectionNormalVelocity

namespace TwoAxisHelicoid
open Set Filter Matrix Complex Topology
open scoped Topology ContDiff

/-- Each point lies in a compact connected set meeting its image under every self-homeomorphism. -/
def HasIntersectingCompactCores (M : Type*) [TopologicalSpace M] : Prop :=
  ∀ p : M, ∃ K : Set M, IsCompact K ∧ IsConnected K ∧ p ∈ K ∧
    ∀ d : M ≃ₜ M, ∃ a ∈ K, d a ∈ K

/-- Setwise involutions of the nearby embedded images have continuous parameter tracks at the central proper slice. -/
theorem compact_core_unmarked_reflections_lift {M E : Type*} [TopologicalSpace M] [T2Space M]
    [MetricSpace E] [ProperSpace E] (o : E) (cores : HasIntersectingCompactCores M)
    {X : ℝ → M → E} (joint : ∀ z, ContinuousAt (fun a : ℝ × M => X a.1 a.2) (0,z))
    (proper : IsProperMap (X 0)) (emb : ∀ᶠ s in 𝓝 (0:ℝ), IsEmbedding (X s))
    {R : E → E} (cont : Continuous R) (inv : Function.Involutive R)
    (symmetric : ∀ᶠ s in 𝓝 (0:ℝ), ∀ p, R (X s p) ∈ range (X s)) :
    ∃ d : ℝ → M ≃ₜ M, (∀ p, ContinuousAt (fun s => d s p) 0) ∧
      ∀ᶠ s in 𝓝 (0:ℝ), ∀ p, X s (d s p) = R (X s p) :=
  unmarked_compact_core_involution_lifts o cores joint proper emb cont inv symmetric

private theorem time_slice_path_smooth {M : Type*} [TopologicalSpace M]
    (X : ℝ → M → Fin 3 → ℝ) (p : M) (e : OpenPartialHomeomorph M ℂ) (hp : p∈e.source)
    (smooth : ContDiffAt ℝ ∞ (fun a : ℝ × ℂ => X a.1 (e.symm a.2)) (0,e p)) :
    ContDiffAt ℝ ∞ (fun s => X s p) 0 := by
  have fixed : ContDiffAt ℝ ∞ (fun s : ℝ => (s,e p)) 0 :=
    contDiff_id.contDiffAt.prodMk contDiffAt_const
  have h := ContDiffAt.comp (f := fun s : ℝ => (s,e p))
    (g := fun a : ℝ × ℂ => X a.1 (e.symm a.2)) 0 smooth fixed
  change ContDiffAt ℝ ∞ (fun s => X s (e.symm (e p))) 0 at h
  rwa [e.left_inv hp] at h

private theorem time_surface_chart_continuity {M : Type*} [TopologicalSpace M]
    (X : ℝ → M → Fin 3 → ℝ) (p : M) (e : OpenPartialHomeomorph M ℂ) (hp : p ∈ e.source)
    (smooth : ContDiffAt ℝ ∞ (fun a : ℝ × ℂ => X a.1 (e.symm a.2)) (0,e p)) :
    ContinuousAt (fun a : ℝ × M => X a.1 a.2) (0,p) := by
  have chart : ContinuousAt (fun a : ℝ × M => (a.1,e a.2)) (0,p) :=
    continuous_fst.continuousAt.prodMk ((e.continuousAt hp).comp (f := (Prod.snd : ℝ × M → M))
      (x := ((0:ℝ),p)) continuous_snd.continuousAt)
  apply (smooth.continuousAt.comp (f := fun a : ℝ × M => (a.1,e a.2))
    (x := ((0:ℝ),p)) chart).congr_of_eventuallyEq
  have source : ∀ᶠ a : ℝ × M in 𝓝 (0,p), a.2 ∈ e.source :=
    continuous_snd.continuousAt.eventually (e.open_source.mem_nhds hp)
  exact source.mono fun a ha => (congrArg (X a.1) (e.left_inv ha)).symm

/-- Oddness of the true normal velocity of an unmarked family. The
central proper slice and the intersecting compact cores supply the continuous
parameters of the reflected points. -/
theorem compact_core_unmarked_reflection_velocity {M : Type*} [TopologicalSpace M] [T2Space M]
    (cores : HasIntersectingCompactCores M) (X : ℝ → M → Fin 3 → ℝ)
    (proper : IsProperMap (X 0))
    (emb : ∀ᶠ s in 𝓝 (0:ℝ), IsEmbedding (X s))
    (e : M → OpenPartialHomeomorph M ℂ) (center : ∀ p, p ∈ (e p).source)
    (smooth : ∀ p, ContDiffAt ℝ ∞ (fun a : ℝ × ℂ => X a.1 ((e p).symm a.2)) (0,e p p))
    (imm : ∀ p, Function.Injective (fderiv ℝ (X 0 ∘ (e p).symm) (e p p)))
    (N : M → Fin 3 → ℝ) (normal : ∀ p h, fderiv ℝ (X 0 ∘ (e p).symm) (e p p) h ⬝ᵥ N p = 0)
    (R : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) (inv : Function.Involutive R)
    (orth : ∀ a b, R a ⬝ᵥ R b = a ⬝ᵥ b)
    (sym : ∀ᶠ s in 𝓝 (0:ℝ), ∀ p, R (X s p) ∈ range (X s))
    (sign : ∀ p q, X 0 q = R (X 0 p) → N q = -R (N p)) :
    let u := fun p => deriv (fun s => X s p) 0 ⬝ᵥ N p
    ∃ ρ : M ≃ₜ M, (∀ p, X 0 (ρ p) = R (X 0 p)) ∧
      (∀ p, u (ρ p) = -u p) ∧ (∀ p, R (X 0 p) = X 0 p → u p = 0) := by
  intro u
  have joint := fun p => time_surface_chart_continuity X p (e p) (center p) (smooth p)
  obtain ⟨d,cont,acts⟩ := compact_core_unmarked_reflections_lift 0 cores joint proper emb
    R.continuous inv sym
  have atZero := acts.self_of_nhds
  have odd (p : M) : u (d 0 p) = -u p := by
    let q := d 0 p
    let c := fun s => e q (d s p)
    have cr : ContinuousAt (fun s => d s p) 0 := cont p
    have hq : d 0 p ∈ (e q).source := center q
    have cc : ContinuousAt c 0 := ((e q).continuousAt hq).comp (f := fun s => d s p) (x := (0:ℝ)) cr
    have track : ∀ᶠ s in 𝓝 (0:ℝ), X s ((e q).symm (c s)) = R (X s p) := by
      filter_upwards [acts, cr.eventually ((e q).open_source.mem_nhds hq)] with s eq near
      exact (congrArg (X s) ((e q).left_inv near)).trans (eq p)
    have vp := time_slice_path_smooth X p (e p) (center p) (smooth p)
    have vq := time_slice_path_smooth X q (e q) (center q) (smooth q)
    apply moving_reflection_normal_velocity_odd
      (F := fun a : ℝ × ℂ => X a.1 ((e q).symm a.2)) (c := c) R orth
      (smooth q) (imm q) cc vp track (vp.differentiableAt (by simp)).hasDerivAt
    · simpa only [c, (e q).left_inv hq] using (vq.differentiableAt (by simp)).hasDerivAt
    · exact normal q
    · exact sign p q (atZero p)
  refine ⟨d 0,atZero,odd,?_⟩
  intro p hp
  have fixed : d 0 p = p := emb.self_of_nhds.injective ((atZero p).trans hp)
  have hu := odd p
  rw [fixed] at hu
  linarith

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_core_unmarked_reflections_lift
#print axioms TwoAxisHelicoid.compact_core_unmarked_reflection_velocity
