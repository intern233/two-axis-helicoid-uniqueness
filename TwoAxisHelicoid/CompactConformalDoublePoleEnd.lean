import TwoAxisHelicoid.CompactPointPuncturedEnd
import TwoAxisHelicoid.OriginalPoleEndTorusReduction
import Mathlib.Geometry.Manifold.LocalDiffeomorph

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology OnePoint Manifold ContDiff

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M]
  [ChartedSpace ℂ (OnePoint M)]

omit [T2Space M] in
/-- On the finite part of any conformal filling the inverse to finite
inclusion is holomorphic. Its arbitrary value at infinity does not enter. -/
theorem conformal_filling_finite_projection (hinc : IsLocalDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
    (OnePoint.some : M → OnePoint M)) (b x : M) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun q : OnePoint M => q.elim b id) (x:OnePoint M) := by
  obtain ⟨D,hx,hD⟩ := hinc x
  have htarget : (x:OnePoint M) ∈ D.target := (hD hx).symm ▸ D.map_source hx
  apply ((D.contMDiffOn_invFun _ htarget).contMDiffAt (D.open_target.mem_nhds htarget)).congr_of_eventuallyEq
  filter_upwards [D.open_target.mem_nhds htarget] with p hp
  have he : (D.symm p : OnePoint M) = p := (hD (D.map_target hp)).trans (D.right_inv hp)
  exact (congrArg (fun q : OnePoint M => q.elim b id) he).symm

/-- The precise conformal filling and actual two poles of
Bernstein--Breiner Theorem 1.1 give the punctured end used in the
original-to-lattice reduction. No height coordinate or end Gauss
exponential expression is part of these hypotheses. -/
theorem conformal_filling_actual_double_pole_end [IsManifold 𝓘(ℂ,ℂ) ω M]
    (b : M) (hinc : IsLocalDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (OnePoint.some : M → OnePoint M))
    (χ : OpenPartialHomeomorph (OnePoint M) ℂ)
    (hχ : χ ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (OnePoint M)) (hp : OnePoint.infty ∈ χ.source) (h0 : χ OnePoint.infty = 0)
    (X : M → Fin 3 → ℝ)
    (hh : MeromorphicAt (fun z => immersionComplexCoefficient ((fun q : OnePoint M => q.elim 0 X) ∘ χ.symm) z 2) 0)
    (hho : meromorphicOrderAt (fun z => immersionComplexCoefficient ((fun q : OnePoint M => q.elim 0 X) ∘ χ.symm) z 2) 0 = -2)
    (hg : MeromorphicAt (immersionGaussLogDerivative ((fun q : OnePoint M => q.elim 0 X) ∘ χ.symm)) 0)
    (hgo : meromorphicOrderAt (immersionGaussLogDerivative ((fun q : OnePoint M => q.elim 0 X) ∘ χ.symm)) 0 = -2) :
    Nonempty (GeometricDoublePoleEnd X) := by
  obtain ⟨E,he,hs,hi⟩ := compact_point_chart_gives_punctured_end b χ hp h0
  have hc : E.coord ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M := by
    apply E.coord.mem_maximalAtlas_of_contMDiffOn
    · intro x hx
      have h := (contMDiffAt_of_mem_maximalAtlas hχ (hs x hx)).comp x (hinc x).contMDiffAt
      exact (h.congr_of_eventuallyEq (Eventually.of_forall he)).contMDiffWithinAt
    · intro w hw
      have hwt : w ∈ χ.target := by
        have h := χ.map_source (hs _ (E.coord.map_target hw))
        rwa [← he,E.coord.right_inv hw] at h
      have h := ((hi w hw) ▸ conformal_filling_finite_projection hinc b (E.coord.symm w)).comp w
        (contMDiffAt_symm_of_mem_maximalAtlas hχ hwt)
      apply ContMDiffAt.contMDiffWithinAt
      apply h.congr_of_eventuallyEq
      filter_upwards [E.coord.open_target.mem_nhds hw] with v hv
      exact congrArg (fun q : OnePoint M => q.elim b id) (hi v hv)
  let V := X ∘ E.coord.symm
  let W := (fun q : OnePoint M => q.elim 0 X) ∘ χ.symm
  have heq : V =ᶠ[𝓝[≠] (0:ℂ)] W := by
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0:ℂ) E.radius_pos),self_mem_nhdsWithin] with w hw hn
    exact congrArg (fun q : OnePoint M => q.elim 0 X) (hi w (E.mem_target_of_ball_ne hw hn))
  obtain ⟨hcoeff,hlog⟩ := spatial_equal_germ_end_coefficients heq
  have hh' := hcoeff.fun_comp (fun A => A 2)
  exact ⟨⟨E,hc,hh.congr hh'.symm,(meromorphicOrderAt_congr hh').trans hho,
    hg.congr hlog.symm,(meromorphicOrderAt_congr hlog).trans hgo⟩⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.conformal_filling_actual_double_pole_end
