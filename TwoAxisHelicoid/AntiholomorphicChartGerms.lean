import TwoAxisHelicoid.PlaneChartOrientationCocycle
import TwoAxisHelicoid.RegularAnalyticSurfaceLift
import TwoAxisHelicoid.AnalyticCauchyRiemannContinuation
import Mathlib.Analysis.Calculus.Deriv.Star

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ComplexConjugate ContDiff Manifold

theorem conjugation_tendsto_punctured_origin : Tendsto conj (𝓝[≠] (0:ℂ)) (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_,?_⟩
  · simpa only [map_zero] using (Complex.continuous_conj.continuousAt (x := (0:ℂ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := ({0}:Set ℂ)ᶜ))
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact fun eq => hz (Complex.conjCLE.injective (eq.trans (map_zero conj).symm))

theorem reflected_analytic_germ {f : ℂ → ℂ} {z : ℂ} (h : AnalyticAt ℂ f z) :
    AnalyticAt ℂ (conj ∘ f ∘ conj) (conj z) := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  have base : Tendsto conj (𝓝 (conj z)) (𝓝 z) := by simpa using (Complex.continuous_conj.continuousAt (x := conj z)).tendsto
  filter_upwards [base.eventually h.eventually_analyticAt] with w hw
  simpa only [starRingEnd_self_apply] using hw.differentiableAt.conj_conj

variable {M : Type*} [TopologicalSpace M]

/-- An antiholomorphic germ tested in any one source and target chart
is antiholomorphic in every pair of compatible conformal charts. -/
theorem antiholomorphic_germ_change_charts [ChartedSpace ℂ M] {f : M → M} (cf : Continuous f) {x : M}
    {a b e d : OpenPartialHomeomorph M ℂ}
    (aa : a∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) (ab : b∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
    (ae : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) (ad : d∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
    (xa : x∈a.source) (xb : f x∈b.source) (xe : x∈e.source) (xd : f x∈d.source)
    (germ : AnalyticAt ℂ (d ∘ f ∘ e.symm ∘ conj) (conj (e x))) :
    AnalyticAt ℂ (b ∘ f ∘ a.symm ∘ conj) (conj (a x)) := by
  let S := e ∘ a.symm
  let V := conj ∘ S ∘ conj
  let G := d ∘ f ∘ e.symm ∘ conj
  let T := b ∘ d.symm
  have sa : AnalyticAt ℂ S (a x) := (complexAtlas_realized_transition aa ae (planeChart_transition_source xa xe)).analyticAt
  have ta : AnalyticAt ℂ T (d (f x)) := (complexAtlas_realized_transition ad ab (planeChart_transition_source xd xb)).analyticAt
  have atz : V (conj (a x))=conj (e x) := by simp only [V,S,Function.comp_apply,starRingEnd_self_apply,a.left_inv xa]
  have gz : G (V (conj (a x)))=d (f x) := by simp only [atz,G,Function.comp_apply,starRingEnd_self_apply,e.left_inv xe]
  have ga : AnalyticAt ℂ G (V (conj (a x))) := atz ▸ germ
  have tr : AnalyticAt ℂ T (G (V (conj (a x)))) := gz ▸ ta
  apply ((tr.comp ga).comp (reflected_analytic_germ sa)).congr
  have lim : Tendsto (a.symm ∘ conj) (𝓝 (conj (a x))) (𝓝 x) := by
    have p := ((a.symm.continuousAt (a.map_source xa)).tendsto.comp
      (show Tendsto conj (𝓝 (conj (a x))) (𝓝 (a x)) by simpa using (Complex.continuous_conj.continuousAt (x := conj (a x))).tendsto))
    simpa only [a.left_inv xa] using p
  filter_upwards [lim.eventually (e.open_source.mem_nhds xe),(cf.continuousAt.tendsto.comp lim).eventually
    (d.open_source.mem_nhds xd)] with z hz hf
  change a.symm (conj z)∈e.source at hz
  change f (a.symm (conj z))∈d.source at hf
  simp only [Function.comp_apply,V,S,G,T,starRingEnd_self_apply]
  rw [e.left_inv hz,d.left_inv hf]

/-- Real analyticity of an induced spatial isometry in the source
parameters, for any source and target chart of a regular embedded map. -/
theorem regular_spatial_lift_chart_analytic {X : M → Fin 3 → ℝ} {R : (Fin 3 → ℝ) → Fin 3 → ℝ}
    {f : M → M} (cf : Continuous f) (space : ∀ x, X (f x)=R (X x)) {a b : OpenPartialHomeomorph M ℂ}
    {z : ℂ} (za : z∈a.target) (zb : f (a.symm z)∈b.source) (ra : AnalyticAt ℝ R (X (a.symm z)))
    (aa : AnalyticAt ℝ (X ∘ a.symm) z) (ab : AnalyticAt ℝ (X ∘ b.symm) (b (f (a.symm z))))
    (inj : Function.Injective (fderiv ℝ (X ∘ b.symm) (b (f (a.symm z))))) :
    AnalyticAt ℝ (b ∘ f ∘ a.symm) z := by
  have c := cf.continuousAt.comp (a.symm.continuousAt za)
  apply continuous_regular_surface_lift_analytic (Y := X ∘ b.symm) (V := R ∘ X ∘ a.symm) ab inj (ra.comp (f := X ∘ a.symm) aa) ((b.continuousAt zb).comp (f := f ∘ a.symm) c)
  filter_upwards [c.eventually (b.open_source.mem_nhds zb)] with w hw
  change f (a.symm w)∈b.source at hw
  change X (b.symm (b (f (a.symm w))))=R (X (a.symm w))
  rw [b.left_inv hw,space]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.antiholomorphic_germ_change_charts
#print axioms TwoAxisHelicoid.regular_spatial_lift_chart_analytic
