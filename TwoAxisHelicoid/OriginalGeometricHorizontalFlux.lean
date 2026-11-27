import TwoAxisHelicoid.RawPublishedConformalPoleReduction
import TwoAxisHelicoid.MarkedHelicoidSphericalFluxRigidity
import TwoAxisHelicoid.OriginalHelicoidRepresentative
import TwoAxisHelicoid.HelicoidEndReparameterization

namespace TwoAxisHelicoid
open Complex Set Filter Topology InnerProductSpace
open scoped Topology ContDiff Manifold

/-- The hypotheses of the nonvertical-flux theorem in the original axis
frame. The given C¹ end is transported by the actual conformal marking. -/
theorem original_graph_has_flux_marking (s : OriginalHelicoidRepresentative)
    (A : PublishedConformalPoleModel s.position) (uniform : CompactGenusOneUniformization.{0} s.modelTorus) :
    ∃ S : ChartedSpace ℂ s.carrier, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω s.carrier ∧ ∃ (L : PeriodPair) (f : s.carrier ≃ₜ PuncturedPeriodTorus L)
      (X : PuncturedPeriodTorus L → Fin 3 → ℝ), ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f ∧
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f.symm ∧ (∀ p, X (f p) = s.position p) ∧ MarkedEmbeddedHelicoidForFlux L X := by
  obtain ⟨S,hM,_,L,f,Y,hf,hi,hpos,hE,_,hreg,_,_⟩ :=
    original_smooth_surface_published_poles_to_torus s.toOriginalSmoothHelicoid uniform A s.positional.1
  let _ := S
  let _ := hM
  let X := fun q : PuncturedPeriodTorus L => Y q.1
  let F := puncturedTorusPullback L X
  have reg (z : ℂ) (hz : z ∉ L.lattice) : (∀ j, HarmonicAt (fun w => F w j) z) ∧
      ConformalCoordinateDerivatives F z ∧ Function.Injective (fderiv ℝ F z) := by
    have e : F =ᶠ[𝓝 z] Y ∘ periodTorusProjection L := by
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
      change w ∉ L.lattice at hw
      simp [F,X,puncturedTorusPullback,hw,puncturedPlaneProjection]
    obtain ⟨harm,con,imm⟩ := hreg z hz
    have der : DifferentiableAt ℝ (Y ∘ periodTorusProjection L) z :=
      (analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (harm j)).differentiableAt
    have eqD : fderiv ℝ F z = fderiv ℝ (Y ∘ periodTorusProjection L) z := e.fderiv_eq
    refine ⟨fun j => (harmonicAt_congr_nhds (e.mono fun w hw => congrFun hw j)).mpr (harm j),?_,by rwa [eqD]⟩
    apply (conformalCoordinateDerivatives_iff_dot (der.congr_of_eventuallyEq e)).mpr
    rw [e.fderiv_eq]
    exact (conformalCoordinateDerivatives_iff_dot der).mp con
  refine ⟨S,hM,L,f,X,hf,hi,hpos,fun z hz => ⟨(reg z hz).1,(reg z hz).2.1⟩,fun z hz => (reg z hz).2.2,
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph.isClosedEmbedding.comp hE,?_⟩
  refine ⟨s.axes.pitch,-1,0,s.axes.pitch_ne,by simp,?_⟩
  have hcoord (v : Fin 3 → ℝ) : axisSpatialNormalization s.axes.pitch_ne ![0,0,0] v = s.axes.pitch • verticalRotation (-1) v := by
    have hzero : (![0,0,0] : Fin 3 → ℝ) = 0 := by ext j; fin_cases j <;> rfl
    rw [hzero,axisSpatialNormalization_apply,map_zero,sub_zero,map_smul]
    congr 1
    ext j
    fin_cases j <;> simp [verticalRotation_apply]
  have eq : ((coordinateToTube ∘ axisSpatialNormalization s.axes.pitch_ne ![0,0,0] ∘ s.position) ∘ f.symm) =
      fun q => coordinateToTube (s.axes.pitch • verticalRotation (-1) (X q)+0) := by
    funext q
    simp only [Function.comp_apply,← hpos,f.apply_symm_apply,hcoord,add_zero,X]
  exact eq ▸ s.graphEnd.comp_homeomorph f.symm

/-- The curve with nonzero horizontal conormal flux is a closed curve on
the original carrier. The flux is computed from its identical spatial
position in the actual conformal marking, in the original axis frame. -/
theorem original_graph_has_horizontal_flux_loop (s : OriginalHelicoidRepresentative)
    (A : PublishedConformalPoleModel s.position) (uniform : CompactGenusOneUniformization.{0} s.modelTorus)
    (bbs : MarkedBernsteinBreinerFluxPrinciple) :
    ∃ (L : PeriodPair) (f : s.carrier ≃ₜ PuncturedPeriodTorus L) (X : PuncturedPeriodTorus L → Fin 3 → ℝ),
      (∀ p, X (f p) = s.position p) ∧ ∃ (p : s.carrier) (γ : Path p p) (q : PuncturedPeriodTorus L) (δ : Path q q)
        (j : Fin 3) (v : ℝ), (∀ t, f (γ t) = δ t) ∧ (∀ t, X (δ t) = s.position (γ t)) ∧
        j ≠ 2 ∧ v ≠ 0 ∧ TorusSpatialConormalIntegral L X j δ v := by
  obtain ⟨_,_,L,f,X,_,_,hpos,h⟩ := original_graph_has_flux_marking s A uniform
  obtain ⟨q,δ,j,v,hj,hv,hn⟩ := bbs L X h
  let γ := δ.map f.symm.continuous
  have e (t : unitInterval) : f (γ t) = δ t := f.apply_symm_apply _
  exact ⟨L,f,X,hpos,_,γ,q,δ,j,v,e,fun t => (e t) ▸ hpos (γ t),hj,hn,hv⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_graph_has_horizontal_flux_loop
