import TwoAxisHelicoid.ConformalPlaneColumns
import TwoAxisHelicoid.CompactChartExtension
import TwoAxisHelicoid.LogGaussMetricConnection
import TwoAxisHelicoid.LogGaussEnergy

namespace TwoAxisHelicoid
open Set Complex Matrix Filter
open scoped Topology ContDiff Manifold

theorem log_gauss_normal_contDiffAt {W : ℂ → ℂ} {z : ℂ} (hW : AnalyticAt ℂ W z) :
    ContDiffAt ℝ ∞ (holomorphicLogGaussNormal W) z := by
  have realAnalytic : AnalyticAt ℝ W z := hW.restrictScalars
  have hr : ContDiffAt ℝ ∞ (fun y => (W y).re) z :=
    reCLM.contDiff.contDiffAt.comp z realAnalytic.contDiffAt
  have hi : ContDiffAt ℝ ∞ (fun y => (W y).im) z :=
    imCLM.contDiff.contDiffAt.comp z realAnalytic.contDiffAt
  apply contDiffAt_pi.mpr
  intro j
  fin_cases j
  · exact hi.cos.div hr.cosh (Real.cosh_pos _).ne'
  · exact hi.sin.div hr.cosh (Real.cosh_pos _).ne'
  · exact hr.sinh.div hr.cosh (Real.cosh_pos _).ne'

theorem log_gauss_normal_perpendicular {X : ℂ → Fin 3 → ℝ} {W : ℂ → ℂ} {z : ℂ}
    (hd : HasFDerivAt X (nullRealDerivative (weierstrassTriple (exp (W z)) 1)) z) (w : ℂ) :
    holomorphicLogGaussNormal W z ⬝ᵥ fderiv ℝ X z w = 0 := by
  let D := nullRealDerivative (weierstrassTriple (exp (W z)) 1)
  obtain ⟨_,ha,hb⟩ := holomorphicLogGaussNormal_actual_weierstrass_normal W z
  change holomorphicLogGaussNormal W z ⬝ᵥ D 1 = 0 at ha
  change holomorphicLogGaussNormal W z ⬝ᵥ D I = 0 at hb
  rw [hd.fderiv]
  change holomorphicLogGaussNormal W z ⬝ᵥ D w = 0
  rw [real_complex_map_columns D w,dotProduct_add,dotProduct_smul,dotProduct_smul,ha,hb]
  simp

/-- A compactly supported smooth scalar multiplied by the geometric Gauss
normal is a smooth global spatial variation field. The normal only needs
to be regular locally along the common compact support. -/
theorem compact_exterior_normal_test_smooth {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] (e : OpenPartialHomeomorph M ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) (c : ℂ) {W : ℂ → ℂ} {u : M → ℝ}
    {P : Set M} (hP : IsCompact P) (hsource : P ⊆ e.source)
    (hs : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ) ∞ u) (ht : tsupport u ⊆ P)
    (hw : ∀ x ∈ P, AnalyticAt ℂ W (e x-c)) :
    ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ (fun x => u x • holomorphicLogGaussNormal W (e x-c)) := by
  intro x
  by_cases hx : x ∈ P
  · have hc := holomorphic_chart_real_contMDiffAt he (hsource hx)
    have hd : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (fun z : ℂ => z-c) (e x) :=
      contMDiffAt_iff_contDiffAt.mpr (contDiffAt_id.sub contDiffAt_const)
    have hn := contMDiffAt_iff_contDiffAt.mpr (log_gauss_normal_contDiffAt (hw x hx))
    exact (hs x).smul (hn.comp x (hd.comp x hc))
  · apply (contMDiffAt_const (c := (0 : Fin 3 → ℝ))).congr_of_eventuallyEq
    filter_upwards [hP.isClosed.isOpen_compl.mem_nhds hx] with y hy
    have hz : u y = 0 := by
      by_contra h
      exact hy (ht (subset_closure h))
    simp only [hz,zero_smul]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_exterior_normal_test_smooth
