import TwoAxisHelicoid.UnivalentAnalyticRegularity
import TwoAxisHelicoid.PlanarRealizationUniformization

namespace TwoAxisHelicoid
open Complex Set Filter Function Topology TopologicalSpace
open scoped Topology ContDiff Manifold

/-- Chart expressions of a holomorphic function are analytic throughout
their domains. A globally injective function has no critical point there. -/
theorem univalent_surface_chart_regular {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {f : M → ℂ} (hol : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f)
    (inj : Injective f) (x : M) (z : ℂ) (hz : z∈(chartAt ℂ x).target) :
    AnalyticAt ℂ (f ∘ (chartAt ℂ x).symm) z ∧ deriv (f ∘ (chartAt ℂ x).symm) z≠0 := by
  let a := chartAt ℂ x
  have an : AnalyticOnNhd ℂ (f ∘ a.symm) a.target := fun w hw =>
    ((hol (a.symm w)).comp w (contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℂ,ℂ)) x) hw)).contDiffAt.analyticAt
  exact ⟨an z hz,univalent_analytic_deriv_ne_zero a.open_target an (inj.injOn.comp a.symm.injOn (mapsTo_univ _ _)) hz⟩

/-- Global univalence alone makes a holomorphic function on an
abstract Riemann surface a biholomorphic local coordinate. -/
theorem univalent_surface_local_biholomorphism {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {f : M → ℂ} (hol : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f)
    (inj : Injective f) : IsLocalDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f := by
  have mapN (x : M) : map f (𝓝 x)=𝓝 (f x) := by
    let a := chartAt ℂ x
    have hx : x∈a.source := mem_chart_source ℂ x
    have ht := a.map_source hx
    obtain ⟨an,reg⟩ := univalent_surface_chart_regular hol inj x (a x) ht
    have e := an.hasStrictDerivAt.map_nhds_eq reg
    change map (f ∘ a.symm) (𝓝 (a x))=𝓝 (f (a.symm (a x))) at e
    rwa [← map_map,a.symm.map_nhds_eq ht,a.left_inv hx] at e
  have emb := isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
    ⟨hol.continuous,inj,isOpenMap_iff_nhds_le.mpr fun x => (mapN x).ge⟩
  intro p
  let _ : Nonempty M := ⟨p⟩
  let e := emb.toOpenPartialHomeomorph f
  have back (y : ℂ) (hy : y∈e.target) : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω e.symm y := by
    let x := e.symm y
    let a := chartAt ℂ x
    let F := f ∘ a.symm
    have hx : x∈a.source := mem_chart_source ℂ x
    have ht := a.map_source hx
    obtain ⟨an,reg⟩ := univalent_surface_chart_regular hol inj x (a x) ht
    let g := an.hasStrictDerivAt.localInverse _ _ _ reg
    have fy : F (a x)=y := (congrArg f (a.left_inv hx)).trans (e.right_inv hy)
    have ag : AnalyticAt ℂ g y := fy ▸ an.analyticAt_localInverse reg
    have gy : g y=a x := fy ▸ (an.hasStrictDerivAt.eventually_left_inverse reg).self_of_nhds
    have smooth := (contMDiffAt_symm_of_mem_maximalAtlas (I:=𝓘(ℂ,ℂ)) (n:=ω)
      (IsManifold.chart_mem_maximalAtlas x) (gy.symm ▸ ht)).comp y ag.contDiffAt.contMDiffAt
    apply smooth.congr_of_eventuallyEq
    have near := (a.continuousAt hx).comp (e.symm.continuousAt hy)
    filter_upwards [e.open_target.mem_nhds hy,(e.symm.continuousAt hy).eventually (a.open_source.mem_nhds hx),
      near.eventually (an.hasStrictDerivAt.eventually_left_inverse reg)] with w hw ha left
    have hfw : F (a (e.symm w))=w := (congrArg f (a.left_inv ha)).trans (e.right_inv hw)
    change e.symm w=a.symm (g w)
    change g (F (a (e.symm w)))=a (e.symm w) at left
    rw [hfw] at left
    rw [left,a.left_inv ha]
  let D : PartialDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) M ℂ ω := {
    toPartialEquiv := e.toPartialEquiv, open_source := e.open_source, open_target := e.open_target,
    contMDiffOn_toFun := hol.contMDiffOn, contMDiffOn_invFun := fun y hy => (back y hy).contMDiffWithinAt }
  exact ⟨D,mem_univ p,fun _ _ => rfl⟩

universe u

/-- The full plane-or-disk classification follows from the existence
of one injective complex-valued holomorphic function on each surface. -/
theorem plane_uniformization_of_univalent_function
    (existence : ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M],
      Nonempty (M ≃ₜ ℂ) → ∃ f : M → ℂ, Injective f ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f) :
    TopologicalPlaneUniformization.{u} := by
  apply plane_uniformization_of_holomorphic_realization
  intro M _ _ _ plane
  obtain ⟨f,inj,hol⟩ := existence M plane
  exact ⟨f,inj,univalent_surface_local_biholomorphism hol inj⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.plane_uniformization_of_univalent_function
