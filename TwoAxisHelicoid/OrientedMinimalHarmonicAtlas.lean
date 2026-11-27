import TwoAxisHelicoid.OrientedMinimalManifold
import TwoAxisHelicoid.MinimalChartComplexData

namespace TwoAxisHelicoid
open Complex Filter Set Matrix InnerProductSpace
open scoped Topology ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

/-- Harmonicity, conformality and regularity of the spatial map in its actual chart. -/
def HarmonicImmersionChart (X : M → Fin 3 → ℝ) (e : OpenPartialHomeomorph M ℂ) : Prop :=
  ∀ z ∈ e.target, (∀ j, HarmonicAt (fun w => X (e.symm w) j) z) ∧
    ConformalCoordinateDerivatives (X ∘ e.symm) z ∧ Function.Injective (fderiv ℝ (X ∘ e.symm) z)

theorem oriented_isothermal_chart_actual_harmonic {F N : M → Fin 3 → ℝ}
    (hr : ∀ x : M, RegularImmersionChart F (chartAt ℂ x))
    (hm : ∀ x : M, coordinateMeanCurvature (F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = 0)
    {e : OpenPartialHomeomorph M ℂ} (he : OrientedIsothermalChart F N e) : HarmonicImmersionChart F e := by
  have hd (z : ℂ) (hz : z ∈ e.target) : ConformalCoordinateDerivatives (F ∘ e.symm) z := by
    obtain ⟨a,ha,hd⟩ := (he.2 _ hz).1
    obtain ⟨hh,hi,_⟩ := conformal_immersion_of_metric_factor _ ha hd
    exact (conformalCoordinateDerivatives_iff_dot ((he.1 z hz).1.differentiableAt (by simp))).mpr ⟨hh,hi⟩
  intro z hz
  have hnear : ∀ᶠ w in 𝓝 z, w ∈ e.target := e.open_target.mem_nhds hz
  have hhar := conformal_minimal_chart_harmonicAt ((he.1 z hz).1.of_le (by norm_num))
    (hnear.mono hd) (hnear.mono fun w hw => (he.1 w hw).2)
    (hnear.mono fun _ hw => minimal_surface_chart_meanCurvature_zero hr hm he.1 hw)
  exact ⟨fun j => hhar.comp_CLM (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ),hd _ hz,(he.1 _ hz).2⟩

/-- Starting with the smooth oriented real immersion and zero geometric mean
curvature, every chart of the induced complex atlas has all three actual
harmonic spatial coordinates and a regular conformal differential. -/
theorem oriented_minimal_induced_harmonic_atlas [IsManifold 𝓘(ℝ,ℂ) ∞ M]
    {F : M → Fin 3 → ℝ} (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F)
    (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) F x)) (ho : PositiveSurfaceAtlas M)
    (hm : ∀ x : M, coordinateMeanCurvature (F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = 0) :
    ∃ S : ChartedSpace ℂ M, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω M ∧ ∀ e ∈ atlas ℂ M, HarmonicImmersionChart F e := by
  have hconv {N : M → Fin 3 → ℝ} {e : OpenPartialHomeomorph M ℂ} (hh : OrientedIsothermalChart F N e) :
      HarmonicImmersionChart F e := oriented_isothermal_chart_actual_harmonic
        (smooth_surface_regular_manifold_chart hF hi) hm hh
  obtain ⟨N,S,_,hs,hchart⟩ := oriented_minimal_manifold_induced_complex_structure hF hi ho hm
  exact ⟨S,hs,fun e he => hconv (hchart e he)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.oriented_minimal_induced_harmonic_atlas
