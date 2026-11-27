import TwoAxisHelicoid.MarkedTorusCircleCoordinates
import TwoAxisHelicoid.PlaneOrientationJacobian
import TwoAxisHelicoid.ComplexEndCompactification
import Mathlib.Geometry.Manifold.SmoothApprox

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff Manifold

/-- The same charted space underlying a Riemann surface is a smooth real
surface. This also applies to arbitrary holomorphic compactifications. -/
theorem complex_curve_underlying_real_manifold (M : Type*) [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] : IsManifold 𝓘(ℝ,ℂ) ∞ M := by
  apply isManifold_of_contDiffOn
  intro e d he hd z hz
  have h := complexAtlas_realized_transition (IsManifold.subset_maximalAtlas he)
    (IsManifold.subset_maximalAtlas hd) hz.1
  exact ((h.restrict_scalars ℝ).of_le (show (∞ : WithTop ℕ∞)≤ω by simp)).contDiffWithinAt

/-- On the original smooth surface a nonvanishing smooth complex map
detects a generator of the marked handle with winding one. Its phase
therefore has no globally continuous real argument. -/
theorem smooth_nonliftable_circle_class {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] [CompactSpace M] [T2Space M] {L : PeriodPair} (mark : M ≃ₜ PeriodTorus L) :
    ∃ (g : M → ℂ) (γ : C(OrientationCircle,M)), ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ g ∧
      (∀ x, g x≠0) ∧ HasOrientationCircleDegree (fun a => planeOrientationDirection (g (γ a))) 1 ∧
      ¬∃ l : C(M,ℝ), ∀ x, (l x : OrientationCircle)=planeOrientationDirection (g x) := by
  let _ := complex_curve_underlying_real_manifold M
  obtain ⟨T,_⟩ := marked_torus_circle_product L
  let coord := mark.trans T
  let f := fun x : M => ((coord x).1 : ℂ)
  have fc : Continuous f := continuous_subtype_val.comp (continuous_fst.comp coord.continuous)
  let γ : C(OrientationCircle,M) := ⟨fun a => coord.symm (orientationCircleHomeomorph a,1),
    coord.symm.continuous.comp (orientationCircleHomeomorph.continuous.prodMk continuous_const)⟩
  have ref (a : OrientationCircle) : f (γ a)=orientationRay a := by
    change ((coord (coord.symm (orientationCircleHomeomorph a,1))).1 : ℂ)=_
    rw [coord.apply_symm_apply]
    rfl
  obtain ⟨g,close,_⟩ := fc.exists_contMDiff_approx 𝓘(ℝ,ℂ) (⊤ : ℕ∞) (ε := fun _ => (1/2:ℝ))
    continuous_const (fun _ => by norm_num)
  have ns (x : M) : g x≠0 := by
    intro zero
    have b := close x
    rw [zero,dist_zero_left,show ‖f x‖=1 from Circle.norm_coe _] at b
    norm_num at b
  have ray (a : OrientationCircle) : planeOrientationDirection (orientationRay a)=a := by
    simpa only [one_smul] using! planeOrientationDirection_scaled_ray zero_lt_one a
  have degree : HasOrientationCircleDegree (fun a => planeOrientationDirection (g (γ a))) 1 := by
    apply circle_degree_small_perturbation (g.2.continuous.comp γ.continuous) orientationRay_continuous
    · simp only [ray]
      exact orientationCircle_degree_id
    · intro a
      have bound := close (γ a)
      rw [dist_eq_norm,ref] at bound
      rw [orientationRay_norm]
      exact bound.trans (by norm_num)
  refine ⟨g,γ,g.2,ns,degree,?_⟩
  rintro ⟨l,hl⟩
  have zero : HasOrientationCircleDegree (fun a => planeOrientationDirection (g (γ a))) 0 := by
    refine ⟨fun t => l (γ (t : OrientationCircle)),l.continuous.comp (γ.continuous.comp QuotientAddGroup.continuous_mk),
      fun t => hl _,fun t => ?_⟩
    change l (γ ((t+1:ℝ):OrientationCircle))=l (γ (t:OrientationCircle))+(0:ℤ)
    rw [AddCircle.coe_add_period]
    simp
  exact (by decide : (1:ℤ)≠0) (degree.unique zero)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_nonliftable_circle_class
