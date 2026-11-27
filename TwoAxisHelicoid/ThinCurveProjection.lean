import TwoAxisHelicoid.HelicoidDistanceTaylor
import TwoAxisHelicoid.HelicoidLocalGraph

set_option autoImplicit false
namespace TwoAxisHelicoid
open Real Set
open scoped Topology ContDiff

/-- Actual curves realizing each unit tangent vector, with the bounds needed
by the thin-tube Taylor estimate. Existence of suitable surface geodesics is
not included in this definition or assumed as an axiom. -/
def HasControlledUnitTangentCurves
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (y : HelicoidTubeCoordinates) (D : E →L[ℝ] HelicoidTubeCoordinates) (ε A : ℝ) : Prop :=
  ∀ u : E, (∑ i, (tubeCartesian (D u) i)^2) = 1 →
    ∃ x v a : ℝ → HelicoidTubeCoordinates,
      x 0 = y ∧ v 0 = D u ∧
      (∀ t ∈ Icc 0 (sqrt ε), HasDerivAt x (v t) t) ∧
      (∀ t ∈ Icc 0 (sqrt ε), HasDerivAt v (a t) t) ∧
      (∀ t ∈ Icc 0 (sqrt ε), x t ∈ helicoidTubeEquiv.target) ∧
      (∀ t ∈ Icc 0 (sqrt ε), |helicoidSignedDistance (x t)| ≤ ε) ∧
      (∀ t ∈ Icc 0 (sqrt ε), (∑ i, (tubeCartesian (v t) i)^2) ≤ 1) ∧
      (∀ t ∈ Icc 0 (sqrt ε), (∑ i, (tubeCartesian (a t) i)^2) ≤ A^2)

theorem tubeCartesian_smul (r : ℝ) (v : HelicoidTubeCoordinates) :
    tubeCartesian (r • v) = r • tubeCartesian v := by
  ext i
  fin_cases i <;> rfl

/-- Thinness and controlled actual tangent curves rule out a normal vector
in the surface tangent plane. This derives transversality from the curve
bounds rather than postulating an angle estimate. -/
theorem thin_curves_projection_derivative_injective
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {y : HelicoidTubeCoordinates} (hy : y ∈ helicoidTubeEquiv.target)
    {D : E →L[ℝ] HelicoidTubeCoordinates} (hD : Function.Injective D)
    {ε A : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1/2) (hA : 0 ≤ A)
    (hthin : (3+A/2)*sqrt ε < 1)
    (hcurves : HasControlledUnitTangentCurves y D ε A) :
    Function.Injective ((fderiv ℝ helicoidBaseCoordinates y).comp D) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro u hu
  obtain ⟨c,hc⟩ := helicoidBaseCoordinates_kernel_normal (v := D u) hy hu
  have hc0 : c = 0 := by
    by_contra hn
    have hunit : tubeCartesian (D (c⁻¹ • u)) = helicoidNormalField y := by
      rw [map_smul,tubeCartesian_smul,hc,smul_smul,inv_mul_cancel₀ hn,one_smul]
    have hnorm : (∑ i, (tubeCartesian (D (c⁻¹ • u)) i)^2) = 1 := by
      rw [hunit,helicoidNormalField_unit]
    obtain ⟨x,v,a,hx0,hv0,hx,hv,hy',hs,hsp,ha⟩ := hcurves (c⁻¹ • u) hnorm
    have hd := helicoid_distance_thin_curve_sqrt_bound hε0 hε hA hx hv hy' hs hsp ha
    have hvn : helicoidDistanceVelocity x v 0 = 1 := by
      unfold helicoidDistanceVelocity
      rw [hx0,hv0,hunit]
      simpa only [pow_two] using helicoidNormalField_unit y
    rw [hvn,abs_one] at hd
    exact (not_le_of_gt hthin) hd
  have hDu : D u = 0 := tubeCartesian_eq_zero_iff.mp (by simpa [hc0] using hc)
  apply hD
  simpa using hDu

/-- The inverse function theorem now applies using the derived
transversality. All assumptions concern the actual parametrization and
actual controlled curves; no mean-curvature or compactification theorem
is silently inserted. -/
theorem thin_curves_surface_projection_local_diffeomorph
    {X : (ℝ × ℝ) → HelicoidTubeCoordinates} {p : ℝ × ℝ}
    (hX : ContDiffAt ℝ (∞ : WithTop ℕ∞) X p)
    (hy : X p ∈ helicoidTubeEquiv.target)
    (hD : Function.Injective (fderiv ℝ X p))
    {ε A : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1/2) (hA : 0 ≤ A)
    (hthin : (3+A/2)*sqrt ε < 1)
    (hcurves : HasControlledUnitTangentCurves (X p) (fderiv ℝ X p) ε A) :
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      p ∈ e.source ∧ (e : (ℝ × ℝ) → ℝ × ℝ) = (fun z => helicoidBaseCoordinates (X z)) ∧
      ContDiffAt ℝ (∞ : WithTop ℕ∞) e.symm (helicoidBaseCoordinates (X p)) := by
  let f : (ℝ × ℝ) → ℝ × ℝ := fun z => helicoidBaseCoordinates (X z)
  let L := (fderiv ℝ helicoidBaseCoordinates (X p)).comp (fderiv ℝ X p)
  have hL : Function.Injective L :=
    thin_curves_projection_derivative_injective hy hD hε0 hε hA hthin hcurves
  let E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
    (LinearEquiv.ofInjectiveEndo L.toLinearMap hL).toContinuousLinearEquiv
  have hf : ContDiffAt ℝ (∞ : WithTop ℕ∞) f p :=
    (helicoidBaseCoordinates_contDiffAt hy).comp p hX
  have hd : HasFDerivAt f (E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p :=
    ((helicoidBaseCoordinates_contDiffAt hy).differentiableAt (by simp)).hasFDerivAt.comp p
      (hX.differentiableAt (by simp)).hasFDerivAt
  let e := hf.toOpenPartialHomeomorph f hd (by simp)
  refine ⟨e,hf.mem_toOpenPartialHomeomorph_source hd (by simp),rfl,?_⟩
  exact hf.to_localInverse hd (by simp)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thin_curves_projection_derivative_injective
#print axioms TwoAxisHelicoid.thin_curves_surface_projection_local_diffeomorph
