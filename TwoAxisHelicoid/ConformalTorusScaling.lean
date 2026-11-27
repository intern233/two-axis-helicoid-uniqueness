import TwoAxisHelicoid.PeriodTorusScaling
import TwoAxisHelicoid.PointedTorusUniformization
import TwoAxisHelicoid.ScaledTorusImmersion

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology Manifold ContDiff

/-- A quotient map lifted by multiplication by a fixed complex number
is holomorphic throughout the compact torus. -/
theorem torus_multiplier_holomorphic (L M : PeriodPair) (c : ℂ)
    (F : PeriodTorus L → PeriodTorus M)
    (hF : ∀ z, F (periodTorusProjection L z) = periodTorusProjection M (c*z)) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F := by
  intro q
  let e := chartAt ℂ q
  have he : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω e q := contMDiffAt_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ q)) (mem_chart_source ℂ q)
  have hm : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun z : ℂ => c*z) (e q) :=
    contMDiffAt_iff_contDiffAt.mpr (contDiffAt_const.mul contDiffAt_id)
  apply ((periodTorusProjection_contMDiff M).contMDiffAt.comp q (hm.comp q he)).congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds (mem_chart_source ℂ q)] with x hx
  change F x = periodTorusProjection M (c*e x)
  rw [← hF]
  exact congrArg F (by
    rw [← periodTorus_chart_symm_eq_projection L q]
    exact (e.left_inv hx).symm)

/-- The same change of scale provides a biholomorphic reparametrization of
the actual punctured immersions, extending across their marked punctures. -/
theorem scaled_harmonic_biholomorphic_correspondence (L M : PeriodPair) (s : ℂ) (hs : s ≠ 0)
    (hp : ∀ z : ℂ, z ∈ L.lattice ↔ s*z ∈ M.lattice) (X : PeriodTorus L → Fin 3 → ℝ)
    (hY : TwoAxisHarmonicConformalImmersion M (fun z => X (periodTorusProjection L (s⁻¹*z)))) :
    ∃ (E : PeriodTorus L ≃ₜ PeriodTorus M) (e : PuncturedPeriodTorus L ≃ₜ PuncturedPeriodTorus M),
      E 0 = 0 ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω E ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω E.symm ∧
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω e ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω e.symm ∧
      (∀ q, (e q).1 = E q.1) ∧ ∀ q, harmonicTorusImmersion hY (e q) = X q.1 := by
  let E := periodTorusScalingHomeomorph L M s hs hp
  have h0 : E 0 = 0 := by change periodTorusProjection M (s*0) = 0; simp
  let e := E.subtype (p := fun q => q ≠ 0) (q := fun q => q ≠ 0) (fun q => by rw [← h0,E.injective.ne_iff])
  have hE := torus_multiplier_holomorphic L M s E (fun _ => rfl)
  have hi := torus_multiplier_holomorphic M L s⁻¹ E.symm (fun _ => rfl)
  refine ⟨E,e,h0,hE,hi,?_,?_,fun _ => rfl,?_⟩
  · intro q
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff (U := puncturedPeriodTorusOpen M) e univ q).mp
    exact (hE.comp (contMDiff_subtype_val (U := puncturedPeriodTorusOpen L))).contMDiffAt.contMDiffWithinAt
  · intro q
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff (U := puncturedPeriodTorusOpen L) e.symm univ q).mp
    exact (hi.comp (contMDiff_subtype_val (U := puncturedPeriodTorusOpen M))).contMDiffAt.contMDiffWithinAt
  · intro q
    obtain ⟨z,hz⟩ := Quotient.exists_rep q.1
    change periodTorusProjection L z = q.1 at hz
    have he : (e q).1 = periodTorusProjection M (s*z) := by change E q.1 = _; rw [← hz]; rfl
    have hn : s*z ∉ M.lattice := fun h => (e q).2 (he.trans ((periodTorusProjection_eq_zero M _).mpr h))
    let r := puncturedPlaneProjection M ⟨s*z,hn⟩
    have hr : e q = r := Subtype.ext he
    rw [hr]
    have hy := harmonicTorusImmersion_projection hY hn
    change harmonicTorusImmersion hY r = X (periodTorusProjection L (s⁻¹*(s*z))) at hy
    simpa only [← mul_assoc,inv_mul_cancel₀ hs,one_mul,hz] using hy

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.scaled_harmonic_biholomorphic_correspondence
