import TwoAxisHelicoid.GeometricEndFromCapDifferentials

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff Manifold

/-- A smaller, analytic change of puncture coordinates, whose source
contains a punctured neighborhood, still has compact complement in the
original surface. Its inverse is the actual inverse of both chart maps. -/
theorem PuncturedComplexEnd.compose_holomorphic_end_chart {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    (E : PuncturedComplexEnd M) (he : E.coord∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
    (d : OpenPartialHomeomorph ℂ ℂ) (tail : d.source∈𝓝[≠] (0:ℂ)) (sub : d.source⊆E.coord.target)
    (fw : ∀ z∈d.source, AnalyticAt ℂ d z) (bw : ∀ z∈d.target, AnalyticAt ℂ d.symm z) :
    let e := E.coord.trans d
    e.target=d.target ∧ IsCompact e.sourceᶜ ∧ e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M := by
  let e := E.coord.trans d
  have target : e.target=d.target := by
    ext z
    exact ⟨And.left,fun hz => ⟨hz,sub (d.map_target hz)⟩⟩
  have original : ∀ᶠ p in cocompact M, p∈E.coord.source := by
    change E.coord.source∈cocompact M
    simpa only [compl_compl] using E.compact_core.compl_mem_cocompact
  have toP : Tendsto E.coord (cocompact M) (𝓝[≠] (0:ℂ)) := tendsto_nhdsWithin_iff.mpr
    ⟨E.to_zero,original.mono fun _ hx => E.coord_ne_zero hx⟩
  have far : e.source∈cocompact M := original.and (toP.eventually tail)
  obtain ⟨C,compact,inc⟩ := mem_cocompact.mp far
  refine ⟨target,compact.of_isClosed_subset e.open_source.isClosed_compl
    (fun z hz => by by_contra h; exact hz (inc h)),?_⟩
  apply e.mem_maximalAtlas_of_contMDiffOn
  · intro z hz
    have sm : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω d (E.coord z) :=
      contMDiffAt_iff_contDiffAt.mpr (fw _ hz.2).contDiffAt
    exact (sm.comp z (contMDiffAt_of_mem_maximalAtlas he hz.1)).contMDiffWithinAt
  · intro z hz
    have sm : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω d.symm z := contMDiffAt_iff_contDiffAt.mpr (bw _ hz.1).contDiffAt
    exact ((contMDiffAt_symm_of_mem_maximalAtlas he hz.2).comp z sm).contMDiffWithinAt

/-- After the physical graph eliminates the winding, the resulting
exponential formula gives a holomorphic representative of dg/g − k dh
in the original puncture chart, including its value at the puncture. -/
theorem logarithmic_remainder_after_winding_elimination {h g H B : ℂ → ℂ} {k : ℂ}
    (hm : MeromorphicAt H 0) (ho : meromorphicOrderAt H 0=(-1:ℤ))
    (ba : AnalyticAt ℂ B 0) (bn : B 0≠0)
    (prim : ∀ᶠ z in 𝓝[≠] (0:ℂ), HasDerivAt H (h z) z)
    (eq : ∀ᶠ z in 𝓝[≠] (0:ℂ), g z=exp (k*H z)*B (H z)⁻¹) :
    ∃ Q : ℂ → ℂ, AnalyticAt ℂ Q 0 ∧ ∀ᶠ z in 𝓝[≠] (0:ℂ), logDeriv g z-k*h z=Q z := by
  obtain ⟨u,ua,un,hH⟩ := (meromorphicOrderAt_eq_int_iff hm).mp ho
  let J := fun z : ℂ => z/u z
  have ja : AnalyticAt ℂ J 0 := analyticAt_id.div ua un
  have j0 : J 0=0 := by simp [J]
  let V := B ∘ J
  have va : AnalyticAt ℂ V 0 := ba.comp_of_eq ja j0
  have vn : V 0≠0 := by simpa only [V,Function.comp_apply,j0] using bn
  have raw : g =ᶠ[𝓝[≠] (0:ℂ)] fun z => exp (k*H z)*V z := by
    filter_upwards [eq,hH,self_mem_nhdsWithin] with z he hh nz
    have hz : H z=u z/z := by simpa [sub_zero,smul_eq_mul,zpow_neg,div_eq_mul_inv,mul_comm] using hh
    simpa only [V,Function.comp_apply,J,hz,inv_div] using he
  refine ⟨fun z => deriv V z/V z,va.deriv.div va vn,?_⟩
  filter_upwards [prim,punctured_germ_eventually_local raw,va.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    (va.continuousAt.eventually_ne vn).filter_mono nhdsWithin_le_nhds] with z dh agree av nv
  have dp := ((dh.const_mul k).cexp).mul av.differentiableAt.hasDerivAt
  have prod : deriv (fun w => exp (k*H w)*V w) z=_ := dp.deriv
  rw [logDeriv_apply,agree.deriv_eq,agree.self_of_nhds,prod]
  field_simp [nv,Complex.exp_ne_zero]
  ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.PuncturedComplexEnd.compose_holomorphic_end_chart
#print axioms TwoAxisHelicoid.logarithmic_remainder_after_winding_elimination
