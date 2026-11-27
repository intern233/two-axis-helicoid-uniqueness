import TwoAxisHelicoid.GeneralHelicoidLogCorrection
import TwoAxisHelicoid.OriginalGeometricExteriorInput
import TwoAxisHelicoid.NormalizedGeometricExteriorCoordinate

namespace TwoAxisHelicoid
open Complex Set Filter Bornology Topology
open scoped Topology ContDiff Manifold

/-- Differential data in the exterior height coordinate from
Bernstein--Breiner, Theorem 1.1 and Corollary 1.2. The pitch is a
real number and the remainder is the holomorphic differential germ.
There is no assumption of a normalized exponential representation. -/
structure FiniteTopologyExteriorDifferential {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (X : M → Fin 3 → ℝ) where
  chart : OpenPartialHomeomorph M ℂ
  radius : ℝ
  positive : 0<radius
  target : chart.target={z : ℂ | radius<‖z‖}
  core : IsCompact chart.sourceᶜ
  holomorphic : chart∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M
  offset : ℝ
  height : ∀ x∈chart.source, X x 2=offset+(chart x).re
  pitch : ℝ
  remainder : ℂ → ℂ
  analytic : AnalyticAt ℂ remainder 0
  gaussPole : let G := fun w : ℂ => immersionGaussMap (X ∘ chart.symm) w⁻¹
    meromorphicOrderAt (logDeriv G) 0=(-2:ℤ)
  differential : let G := fun w : ℂ => immersionGaussMap (X ∘ chart.symm) w⁻¹
    ∀ᶠ w in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ G w ∧ G w≠0 ∧
      logDeriv G w-I*(pitch:ℂ)*((-1:ℂ)/w^2)=remainder w

/-- Integrate the actual differential in its puncture coordinate and
recover a geometric Weierstrass exterior on the original surface. -/
noncomputable def FiniteTopologyExteriorDifferential.toExterior {M : Type*} [TopologicalSpace M]
    [ChartedSpace ℂ M] {X : M → Fin 3 → ℝ} (A : FiniteTopologyExteriorDifferential X) :
    GeometricExteriorCoordinate X := by
  let G := fun w : ℂ => immersionGaussMap (X ∘ A.chart.symm) w⁻¹
  have data : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ G z ∧ G z≠0 ∧
      HasDerivAt (fun w : ℂ => w⁻¹) ((-1:ℂ)/z^2) z ∧
      logDeriv G z-I*(A.pitch:ℂ)*((-1:ℂ)/z^2)=A.remainder z := by
    filter_upwards [A.differential,self_mem_nhdsWithin] with z hz nz
    exact ⟨hz.1,hz.2.1,by simpa only [neg_div,one_div] using! hasDerivAt_inv (show z≠0 from nz),hz.2.2⟩
  have non := logarithmic_gauss_pole_forces_pitch A.gaussPole A.analytic (data.mono fun _ h => h.2.2.2)
  have witness := holomorphic_log_difference_integrates A.analytic data
  let F := Classical.choose witness
  have properties := Classical.choose_spec witness
  refine ⟨A.chart,A.radius,A.positive,A.target,A.core,A.holomorphic,A.offset,A.height,
    A.pitch,non,F,properties.1,?_⟩
  filter_upwards [tendsto_inv₀_cobounded'.eventually properties.2] with z hz
  simpa only [G,inv_inv] using hz.2

/-- No rotation or scaling of the physical immersion is needed when
making the integrated correction vanish by a height-coordinate shift. -/
theorem FiniteTopologyExteriorDifferential.normalized {M : Type*} [TopologicalSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {X : M → Fin 3 → ℝ}
    (A : FiniteTopologyExteriorDifferential X) (cx : Continuous X) (tails : HasConnectedCompactTails M) :
    ∃ B : GeometricExteriorCoordinate X, B.pitch=A.pitch ∧ B.correction 0=0 :=
  A.toExterior.normalized cx tails

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.FiniteTopologyExteriorDifferential.toExterior
#print axioms TwoAxisHelicoid.FiniteTopologyExteriorDifferential.normalized
