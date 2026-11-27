import TwoAxisHelicoid.MaximalHarmonicImmersionChart

namespace TwoAxisHelicoid
open Complex Set Filter Topology InnerProductSpace
open scoped Topology OnePoint ContDiff Manifold

/-- Extending the parametrization by an arbitrary value at the added point
preserves harmonicity in every complex coordinate of the compactification
at every original finite point. -/
theorem filled_chart_harmonic_at_finite_point {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    {X : M → Fin 3 → ℝ} (charts : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e)
    (E : PuncturedComplexEnd M) (hol : E.coord∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) (v : Fin 3 → ℝ) :
    let _ := compactifiedEndAtlas E
    ∀ e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (OnePoint M), ∀ z∈e.target, e.symm z≠OnePoint.infty →
      ∀ j : Fin 3, HarmonicAt (fun w => (e.symm w).elim v X j) z := by
  let _ := compactifiedEndAtlas E
  let _ := compactifiedEndAtlas_isManifold E hol
  dsimp only
  intro e he z hz finite j
  obtain ⟨x,eq⟩ := OnePoint.ne_infty_iff_exists.mp finite
  let q := chartAt ℂ x
  let d := finiteOnePointChart q
  have atlas : d∈atlas ℂ (OnePoint M) := Or.inl ⟨q,chart_mem_atlas ℂ x,rfl⟩
  have src : e.symm z∈d.source := eq ▸ (finiteOnePointChart_coe_source q x).mpr (mem_chart_source ℂ x)
  let u := e.symm.trans d
  have hz' : z∈u.source := ⟨hz,src⟩
  have hu := (complexAtlas_realized_transition he (IsManifold.subset_maximalAtlas atlas) hz').analyticAt
  have h := (charts q (chart_mem_atlas ℂ x) (u z) (d.map_source src)).1 j
  have germ : (fun w => (e.symm w).elim v X j) =ᶠ[𝓝 z] (fun w => X (q.symm w) j) ∘ u := by
    filter_upwards [u.open_source.mem_nhds hz'] with w hw
    exact congrArg (fun p : OnePoint M => p.elim v X j) (d.left_inv hw.2).symm
  exact (harmonicAt_congr_nhds germ).mpr (harmonic_scalar_comp_analytic h hu)

/-- The physical harmonic coordinates themselves determine compatible
holomorphic one-form coefficients throughout the punctured compact surface. -/
theorem filled_chart_physical_coefficient_law {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    {X : M → Fin 3 → ℝ} (charts : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e)
    (E : PuncturedComplexEnd M) (hol : E.coord∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) (v : Fin 3 → ℝ) (j : Fin 3) :
    let _ := compactifiedEndAtlas E
    let a := fun (e : OpenPartialHomeomorph (OnePoint M) ℂ) z =>
      immersionComplexCoefficient (fun w => (e.symm w).elim v X) z j
    (∀ e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (OnePoint M), ∀ z∈e.target, e.symm z≠OnePoint.infty → AnalyticAt ℂ (a e) z) ∧
    ∀ e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (OnePoint M), ∀ d∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (OnePoint M),
      ∀ z∈(e.symm.trans d).source, e.symm z≠OnePoint.infty →
        a e z=a d ((e.symm.trans d) z)*deriv (e.symm.trans d) z := by
  let _ := compactifiedEndAtlas E
  let _ := compactifiedEndAtlas_isManifold E hol
  let F := fun p : OnePoint M => p.elim v X
  let h := filled_chart_harmonic_at_finite_point charts E hol v
  constructor
  · intro e he z hz finite
    exact scalarComplexCoefficient_analyticAt (h e he z hz finite j)
  · intro e he d hd z hz finite
    let u := e.symm.trans d
    have hu := (complexAtlas_realized_transition he hd hz).analyticAt
    have finite' : d.symm (u z)≠OnePoint.infty := (d.left_inv hz.2).trans_ne finite
    have diff : DifferentiableAt ℝ (F ∘ d.symm) (u z) :=
      (analyticAt_pi_iff.mpr (fun k => _root_.HarmonicAt.analyticAt (h d hd _ (d.map_source hz.2) finite' k))).differentiableAt
    have germ : (fun w => F (e.symm w) j) =ᶠ[𝓝 z] fun w => F (d.symm (u w)) j := by
      filter_upwards [u.open_source.mem_nhds hz] with w hw
      exact congrArg (fun p => F p j) (d.left_inv hw.2).symm
    have coeff : immersionComplexCoefficient (F ∘ e.symm) z j=immersionComplexCoefficient ((F ∘ d.symm) ∘ u) z j := by
      exact congrArg (fun L : ℂ →L[ℝ] ℝ => (L 1 : ℂ)-I*(L I : ℂ)) (germ.fderiv_eq (𝕜:=ℝ))
    exact coeff.trans ((immersionComplexCoefficient_comp_holomorphic diff hu.differentiableAt.hasDerivAt j).trans (mul_comm _ _))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.filled_chart_harmonic_at_finite_point
#print axioms TwoAxisHelicoid.filled_chart_physical_coefficient_law
