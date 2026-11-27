import TwoAxisHelicoid.GenusOneFromAnnularUniformization
import TwoAxisHelicoid.CompactHarmonicCircleUniformization

namespace TwoAxisHelicoid
open Complex Set Function Filter Topology
open scoped Topology ContDiff Manifold

/-- The first lattice coordinate modulo one, pulled back by the actual
biholomorphism, has harmonic local arguments and period one on the
first marked circle. It supplies a nonzero global cotangent section
in the original complex structure. -/
theorem uniformized_torus_has_holomorphic_differential {M : Type*} [TopologicalSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] (uniform : AdmitsPeriodTorusUniformization M) :
    ∃ w : holomorphicCotangentSections M, w≠0 := by
  obtain ⟨L,H,hol,_⟩ := uniform
  let _ : ConnectedSpace (PeriodTorus L) := (Quotient.mk_surjective :
    Surjective (periodTorusProjection L)).connectedSpace QuotientAddGroup.continuous_mk
  let _ : ConnectedSpace M := H.symm.surjective.connectedSpace H.symm.continuous
  let A := (L.basis.coord (0:Fin 2)).toContinuousLinearMap
  let F := fun z : ℂ => (A z : OrientationCircle)
  have periodic (z w : ℂ) (hw : w∈L.lattice) : F (z+w)=F z := by
    obtain ⟨m,_,hm,_⟩ := (integral_period_coordinates_iff L w).mp hw
    have v : A w=(m:ℝ) := hm
    change ((A (z+w) : ℝ) : OrientationCircle)=_
    rw [map_add,AddCircle.coe_add,v,orientationCircle_int_zero,add_zero]
  let φ := periodTorusLift L F periodic ∘ H
  have ha : HasLocalHarmonicArguments φ := by
    intro x
    let e := chartAt ℂ x
    let b := chartAt ℂ (H x)
    let G := b ∘ H ∘ e.symm
    let z := e x
    have src : x∈e.source := mem_chart_source _ _
    have tar : z∈e.target := e.map_source src
    have eq : e.symm z=x := e.left_inv src
    have bs : H (e.symm z)∈b.source := eq.symm ▸ mem_chart_source ℂ (H x)
    have ce := contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℂ,ℂ)) (n := ω)
      (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ x)) tar
    have cb := contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℂ,ℂ)) (n := ω)
      (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ (H x))) bs
    have analytic : AnalyticAt ℂ G z := (contMDiffAt_iff_contDiffAt.mp
      (cb.comp z ((hol (e.symm z)).comp z ce))).analyticAt
    refine ⟨A ∘ G,analytic.harmonicAt.comp_CLM A,?_⟩
    filter_upwards [(hol (e.symm z)).continuousAt.comp (e.symm.continuousAt tar) |>.eventually
      (b.open_source.mem_nhds bs)] with w hw
    have pr : periodTorusProjection L (G w)=H (e.symm w) := by
      change periodTorusProjection L (b (H (e.symm w)))=_
      rw [← periodTorus_chart_symm_eq_projection L (H x)]
      exact b.left_inv hw
    change F (G w)=periodTorusLift L F periodic (H (e.symm w))
    rw [← pr,periodTorusLift_projection]
  apply harmonic_nonliftable_phase_gives_holomorphic_section ha
  rintro ⟨u,lift⟩
  let z := fun t : ℝ => spinSquareLinear L t 0
  let k := fun t : ℝ => u (H.symm (periodTorusProjection L (z t)))
  have cz : Continuous z := by dsimp [z,spinSquareLinear]; fun_prop
  have ck : Continuous k := u.continuous.comp (H.symm.continuous.comp (QuotientAddGroup.continuous_mk.comp cz))
  have agrees (t : ℝ) : (k t : OrientationCircle)=(t : OrientationCircle) := by
    change (u (H.symm _) : OrientationCircle)=_
    rw [lift]
    change periodTorusLift L F periodic (H (H.symm (periodTorusProjection L (z t))))=_
    rw [H.apply_symm_apply,periodTorusLift_projection]
    exact congrArg (fun r : ℝ => (r : OrientationCircle)) (spinSquareLinear_coords L t 0).1
  obtain ⟨n,inc⟩ := orientationCircle_lifts_difference ck continuous_id agrees 0
  have period : k 1=k 0 := by
    apply congrArg u
    apply congrArg H.symm
    change periodTorusProjection L (spinSquareLinear L 1 0)=periodTorusProjection L (spinSquareLinear L 0 0)
    simp only [spinSquareLinear,one_smul,zero_smul,add_zero,periodTorusProjection,L.basis_zero]
    exact (QuotientAddGroup.eq_zero_iff _).mpr L.ω₁_mem_lattice
  have low := inc 0
  have high := inc 1
  change k 0=(0:ℝ)+n at low
  change k 1=(1:ℝ)+n at high
  linarith

universe u

theorem genus_one_holomorphic_differential_from_annuli (ann : AnnularRiemannSurfaceUniformization.{0}) :
    GenusOneHasHolomorphicDifferential.{u} := by
  intro L M top compact sep atlas manifold marking
  exact uniformized_torus_has_holomorphic_differential
    (compact_genus_one_uniformization_of_annular_classification ann L M marking)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.uniformized_torus_has_holomorphic_differential
#print axioms TwoAxisHelicoid.genus_one_holomorphic_differential_from_annuli
