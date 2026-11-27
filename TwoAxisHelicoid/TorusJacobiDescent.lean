import TwoAxisHelicoid.MinimalSimilarityJacobi
import TwoAxisHelicoid.ActualTorusManifoldImmersion
import TwoAxisHelicoid.TorusHeightFluxLoop

namespace TwoAxisHelicoid
open Complex Matrix Set Filter Topology InnerProductSpace
open scoped Topology ContDiff Manifold

/-- In the translation atlas of a marked torus the entire derivative, and
hence its oriented unit normal, is independent of the lift. -/
theorem marked_normal_periodic (L : PeriodPair) (X : PeriodTorus L → Fin 3 → ℝ)
    (z v : ℂ) (hv : v ∈ L.lattice) : harmonicChartNormal (X ∘ periodTorusProjection L) (z+v) =
      harmonicChartNormal (X ∘ periodTorusProjection L) z := by
  let Y := X ∘ periodTorusProjection L
  have he : (fun w => Y (w+v)) = Y := funext fun w => congrArg X (periodTorusProjection_add_lattice L w v hv)
  have hd : fderiv ℝ Y (z+v) = fderiv ℝ Y z := by rw [← fderiv_comp_add_right (f := Y) v,he]
  change (fderiv ℝ Y (z+v) 1 ⬝ᵥ fderiv ℝ Y (z+v) 1)⁻¹ • (fderiv ℝ Y (z+v) 1 ⨯₃ fderiv ℝ Y (z+v) I) = _
  rw [hd]
  rfl

noncomputable def markedSimilarityJacobiField (L : PeriodPair) (X : PeriodTorus L → Fin 3 → ℝ)
    (a b : Fin 3 → ℝ) (d : ℝ) : PeriodTorus L → ℝ :=
  let Y := X ∘ periodTorusProjection L
  periodTorusLift L (similarityNormal Y (harmonicChartNormal Y) a b d) (fun z v hv => by
    unfold similarityNormal
    simp only [Y,Function.comp_apply,periodTorusProjection_add_lattice L z v hv,marked_normal_periodic L X z v hv])

theorem markedSimilarityJacobiField_at_lift (L : PeriodPair) (X : PeriodTorus L → Fin 3 → ℝ)
    (a b : Fin 3 → ℝ) (d : ℝ) (z : ℂ) :
    markedSimilarityJacobiField L X a b d (periodTorusProjection L z) =
      similarityNormal (X ∘ periodTorusProjection L) (harmonicChartNormal (X ∘ periodTorusProjection L)) a b d z := rfl

theorem periodic_analytic_scalar_on_punctured_torus (L : PeriodPair) (F : ℂ → ℝ)
    (hp : ∀ z v, v ∈ L.lattice → F (z+v) = F z) (hF : ∀ z ∉ L.lattice, AnalyticAt ℝ F z) :
    ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ) ω (fun q : PuncturedPeriodTorus L => periodTorusLift L F hp q.1) := by
  intro p
  let q := p.1
  let z := chartAt ℂ q q
  have he : periodTorusProjection L z = q := periodTorus_chart_representative L q
  have hz : z ∉ L.lattice := fun h => p.2 (he.symm.trans ((periodTorusProjection_eq_zero L z).mpr h))
  have ha : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ) ω (periodTorusLift L F hp) q := by
    apply contMDiffAt_iff.mpr
    refine ⟨?_,?_⟩
    · rw [← he]
      exact periodTorusLift_continuousAt L F hp (hF z hz).continuousAt
    · have hh : ContDiffAt ℝ ω (periodTorusLift L F hp ∘ (chartAt ℂ q).symm) z := by
        rw [periodTorus_chart_symm_eq_projection L q]
        exact (hF z hz).contDiffAt
      simpa only [mfld_simps] using! hh.contDiffWithinAt (s := range 𝓘(ℝ,ℂ))
  exact ha.comp p (contMDiff_subtype_val (U := puncturedPeriodTorusOpen L)).contMDiffAt

/-- Smoothness and the Jacobi equation are properties of functions on the
actual punctured surface. In every marked covering chart the operator is the
induced metric Laplacian plus the squared norm of the second fundamental form. -/
def IsSmoothMarkedJacobiField (L : PeriodPair) (X : PeriodTorus L → Fin 3 → ℝ)
    (u : PuncturedPeriodTorus L → ℝ) : Prop :=
  ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ) ∞ u ∧ ∀ z ∉ L.lattice,
    conformalSurfaceJacobi (X ∘ periodTorusProjection L) (puncturedTorusPullback L u) z = 0

theorem markedSimilarityJacobiField_isJacobi (L : PeriodPair) (X : PeriodTorus L → Fin 3 → ℝ)
    (hY : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => X (periodTorusProjection L w) j) z) ∧
      ConformalCoordinateDerivatives (X ∘ periodTorusProjection L) z ∧
      Function.Injective (fderiv ℝ (X ∘ periodTorusProjection L) z))
    (a b : Fin 3 → ℝ) (d : ℝ) :
    IsSmoothMarkedJacobiField L X (fun q : PuncturedPeriodTorus L => markedSimilarityJacobiField L X a b d q.1) := by
  let Y := X ∘ periodTorusProjection L
  let N := harmonicChartNormal Y
  let u := similarityNormal Y N a b d
  have hx (z : ℂ) (hz : z ∉ L.lattice) : AnalyticAt ℝ Y z :=
    analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt ((hY z hz).1 j)
  constructor
  · apply ContMDiff.of_le (n := ω) _ (by simp)
    refine periodic_analytic_scalar_on_punctured_torus L u (fun z v hv => ?_) ?_
    · simp only [u,N,Y,similarityNormal,Function.comp_apply,
        periodTorusProjection_add_lattice L z v hv,marked_normal_periodic L X z v hv]
    intro z hz
    have hN := (harmonicChartNormal_data (hx z hz) (hY z hz).2.1 (hY z hz).2.2).1
    have ha : AnalyticAt ℝ (fun w => a+similarityLinear b d (Y w)) z :=
      analyticAt_const.add (((similarityLinear b d).analyticAt _).comp (hx z hz))
    have hd := (spatialDotBilinear.analyticAt_bilinear _).comp₂ ha hN
    convert hd using 1
    funext w
    change (a+b ⨯₃ Y w+d • Y w) ⬝ᵥ N w = (a+(b ⨯₃ Y w+d • Y w)) ⬝ᵥ N w
    rw [add_assoc]
  · intro z hz
    have hn : ∀ᶠ w in 𝓝 z, w ∉ L.lattice := L.isClosed_lattice.isOpen_compl.mem_nhds hz
    have he : puncturedTorusPullback L (fun q : PuncturedPeriodTorus L => markedSimilarityJacobiField L X a b d q.1) =ᶠ[𝓝 z] u := by
      filter_upwards [hn] with w hw
      simp only [puncturedTorusPullback,dite_eq_left hw]
      exact markedSimilarityJacobiField_at_lift L X a b d w
    unfold conformalSurfaceJacobi
    rw [(laplacian_congr_nhds he).self_of_nhds,he.self_of_nhds]
    exact similarity_normal_solves_jacobi (hn.mono fun w hw => hY w hw) a b d

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.markedSimilarityJacobiField_isJacobi
