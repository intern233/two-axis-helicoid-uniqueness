import TwoAxisHelicoid.SmoothMinimalVariationJacobi
import TwoAxisHelicoid.GeometricHelicoidHypotheses
import TwoAxisHelicoid.PuncturedTorusRealOrientation
import TwoAxisHelicoid.OrientedHarmonicNormal

namespace TwoAxisHelicoid
open Set Filter Complex Matrix Topology InnerProductSpace Laplacian
open scoped Topology ContDiff Manifold

/-- D.1 for an actual geometric surface. Both joint regularity of the family
and vanishing mean curvature are measured in its given real chart at each
point. A central isothermal atlas and one compatible unit normal are obtained
from the immersion itself. -/
theorem OriginalSmoothHelicoid.minimal_family_velocity_jacobi (base : OriginalSmoothHelicoid)
    (X : ℝ → base.carrier → Fin 3 → ℝ) (atZero : X 0 = base.position)
    (family : ∀ p, ContDiffAt ℝ 3
      (fun a : ℝ × ℂ => X a.1 ((chartAt ℂ p).symm a.2)) (0,chartAt ℂ p p))
    (minimal : ∀ p, ∀ᶠ r in 𝓝 (0:ℝ),
      coordinateMeanCurvature (X r ∘ (chartAt ℂ p).symm) (chartAt ℂ p p) = 0) :
    ∃ N : base.carrier → Fin 3 → ℝ, Continuous N ∧ (∀ x, N x ⬝ᵥ N x = 1) ∧
      ∃ S : ChartedSpace ℂ base.carrier, let _ := S
        IsManifold 𝓘(ℂ,ℂ) ω base.carrier ∧ ∀ e ∈ atlas ℂ base.carrier,
          HarmonicImmersionChart base.position e ∧ ∀ z ∈ e.target,
            N (e.symm z) = harmonicChartNormal (base.position ∘ e.symm) z ∧
            conformalSurfaceJacobi (base.position ∘ e.symm)
              ((fun p => deriv (fun r => X r p) 0 ⬝ᵥ N p) ∘ e.symm) z = 0 := by
  have old := smooth_surface_regular_manifold_chart base.smooth base.immersion
  obtain ⟨V,_,S,analytic,charts⟩ := punctured_torus_minimal_induced_oriented_atlas
    base.topologicalType base.smooth base.immersion base.minimal
  obtain ⟨N,normal,unit,cn⟩ := @oriented_harmonic_atlas_unit_normal _ _ S base.position V charts
  refine ⟨N,cn,unit,S,analytic,?_⟩
  intro e he
  refine ⟨(charts e he).2,?_⟩
  intro z hz
  refine ⟨normal e he z hz,?_⟩
  let p := e.symm z
  let d := base.charts.chartAt p
  let t := e.symm.trans d
  have src : z ∈ t.source := ⟨hz, base.charts.mem_chart_source p⟩
  have smoothT := regularImmersionChart_transition (charts e he).1.1 (old p) src
  have germ (r : ℝ) : (X r ∘ e.symm) =ᶠ[𝓝 z] ((X r ∘ d.symm) ∘ t) := by
    filter_upwards [t.open_source.mem_nhds src] with w hw
    exact congrArg (X r) (d.left_inv hw.2).symm
  have joint : ContDiffAt ℝ 3 (fun q : ℝ × ℂ => X q.1 (e.symm q.2)) (0,z) := by
    have change : ContDiffAt ℝ 3 (fun q : ℝ × ℂ => (q.1,t q.2)) (0,z) :=
      contDiffAt_fst.prodMk ((smoothT.of_le (by simp)).comp (0,z) contDiffAt_snd)
    apply ((family p).comp (0,z) change).congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.eventually (t.open_source.mem_nhds src)] with q hq
    exact congrArg (X q.1) (d.left_inv hq.2).symm
  have cm : ∀ᶠ r in 𝓝 (0:ℝ), coordinateMeanCurvature (X r ∘ e.symm) z = 0 := by
    have near : ∀ᶠ r in 𝓝 (0:ℝ), ContDiffAt ℝ 3
        (fun a : ℝ × ℂ => X a.1 (d.symm a.2)) (r,d p) :=
      ((continuous_id.prodMk continuous_const).tendsto 0).eventually ((family p).eventually (by norm_num))
    filter_upwards [near,minimal p] with r hr hm
    have cr : ContDiffAt ℝ 2 (X r ∘ d.symm) (t z) :=
      (hr.of_le (show (2:ℕ∞ω) ≤ 3 by norm_num)).comp (t z) (contDiffAt_const.prodMk contDiffAt_id)
    rw [coordinateMeanCurvature_congr (germ r)]
    exact minimal_surface_reparametrization cr (smoothT.of_le (by norm_num)) hm
  have baseGerm : ∀ᶠ w in 𝓝 z, (∀ j, HarmonicAt (fun y => (base.position ∘ e.symm) y j) w) ∧
      ConformalCoordinateDerivatives (base.position ∘ e.symm) w ∧
        Function.Injective (fderiv ℝ (base.position ∘ e.symm) w) := by
    filter_upwards [e.open_target.mem_nhds hz] with w hw using (charts e he).2 w hw
  have jac := smooth_minimal_variation_normal_jacobi (F := fun r => X r ∘ e.symm) joint
    (by simpa only [atZero] using baseGerm) cm
  rw [atZero] at jac
  have agree : ((fun x => deriv (fun r => X r x) 0 ⬝ᵥ N x) ∘ e.symm) =ᶠ[𝓝 z]
      (fun w => deriv (fun r => X r (e.symm w)) 0 ⬝ᵥ harmonicChartNormal (base.position ∘ e.symm) w) := by
    filter_upwards [e.open_target.mem_nhds hz] with w hw
    simp only [Function.comp_apply,normal e he w hw]
  unfold conformalSurfaceJacobi at jac ⊢
  rwa [(laplacian_congr_nhds agree).self_of_nhds,agree.self_of_nhds]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.OriginalSmoothHelicoid.minimal_family_velocity_jacobi
