import TwoAxisHelicoid.RawPublishedConformalPoleReduction
import TwoAxisHelicoid.OriginalExteriorTorusReduction
import TwoAxisHelicoid.SchwarzNormalizedImmersion
import TwoAxisHelicoid.ScaledTorusImmersion
import TwoAxisHelicoid.UnorientedIsothermalChartHarmonic
import TwoAxisHelicoid.HelicoidEndReparameterization

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology ContDiff Manifold OnePoint
set_option maxHeartbeats 1800000

/-- A holomorphic puncture of the original harmonic conformal surface,
together with compact genus-one uniformization, places its actual two
straight axes in a rhombic marking. Spatial coordinates and the
prescribed asymptotic helicoid are unaffected by this change of domain. -/
theorem conformally_filled_actual_rhombic_marking {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {L₀ : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L₀)
    (uniform : CompactGenusOneUniformization.{0} L₀)
    (X : M → Fin 3 → ℝ) (hX : IsClosedEmbedding X) (hchart : ∀ d∈atlas ℂ M, HarmonicImmersionChart X d)
    (E : PuncturedComplexEnd M) (hol : E.coord∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
    (horizontal : ∀ r : ℝ, (![r,0,0] : Fin 3 → ℝ)∈range X)
    (vertical : ∀ r : ℝ, (![0,0,r] : Fin 3 → ℝ)∈range X)
    : ∃ (t : ℝ) (ht : 0<t) (Z : ℂ → Fin 3 → ℝ)
      (hZ : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) Z)
      (g : M ≃ₜ PuncturedPeriodTorus (rhombicPeriodPair t ht)), X ∘ g.symm=harmonicTorusImmersion hZ := by
  have hlc : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ℂ M
  let _ := compactifiedEndAtlas E
  have hm : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint M) := compactifiedEndAtlas_isManifold E hol
  let T := top.onePointCongr.trans (punctureCompactification (0:PeriodTorus L₀))
  obtain ⟨L,H,h0,hH,hi,_,_⟩ := compactified_uniformization_restricts E (uniform (OnePoint M) ⟨T⟩)
  let f := markedPuncturedUniformization H h0
  let Y := fun q : PeriodTorus L => (H.symm q).elim 0 X
  have fin (x : M) : Y (f x).1=X x := by change (H.symm (H (x:OnePoint M))).elim 0 X=X x; rw [H.symm_apply_apply]; rfl
  obtain ⟨close,image⟩ := marked_immersion_closedEmbedding_range H h0 X hX 0
  have regular := marked_harmonic_immersion_coordinates E X 0 hchart hm H h0 hH hi
  obtain ⟨s,t,hs,ht,period,Z⟩ := straight_axes_to_two_axis_harmonic_immersion L Y close
    (fun r => image.symm ▸ horizontal r) (fun r => image.symm ▸ vertical r) regular
  obtain ⟨e,he⟩ := scaled_harmonic_quotient_correspondence L (rhombicPeriodPair t ht) s hs period Y Z
  let g := f.trans e
  let F := harmonicTorusImmersion Z
  have pos (q : PuncturedPeriodTorus (rhombicPeriodPair t ht)) : X (g.symm q)=F q := by
    change X (f.symm (e.symm q))=F q
    rw [← fin (f.symm (e.symm q)),f.apply_symm_apply,← he (e.symm q),e.apply_symm_apply]
  have eq : X ∘ g.symm=F := funext pos
  exact ⟨t,ht,_,Z,g,eq⟩

/-- The unmarked real surface inherits a holomorphic puncture and
harmonic conformal charts from its compact conformal end model. -/
theorem published_poles_original_holomorphic_puncture (s : OriginalSmoothHelicoid)
    (D : PublishedConformalPoleModel s.position) :
    ∃ S : ChartedSpace ℂ s.carrier, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω s.carrier ∧ (∀ d∈atlas ℂ s.carrier, HarmonicImmersionChart s.position d) ∧
      ∃ E : PuncturedComplexEnd s.carrier, E.coord∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω s.carrier := by
  have transfer {e : OpenPartialHomeomorph s.carrier ℂ} (he : InducedIsothermalChart s.position e) :=
    real_minimal_isothermal_chart_harmonic s.smooth s.immersion s.minimal he
  obtain ⟨S,hm,he,hj⟩ := puncture_pullback_isothermal_atlas D.point D.marking s.position D.spatial D.agrees D.isothermal
  let _ := S
  have hman : IsManifold 𝓘(ℂ,ℂ) ω s.carrier := hm
  obtain ⟨base,_⟩ := s.axes.vertical 0
  let W := fun x => D.offset+D.frame (s.position x)
  let Y := fun q => D.offset+D.frame (D.spatial q)
  have point (x : s.carrier) : Y (D.marking x).1=W x := congrArg (fun v => D.offset+D.frame v) (D.agrees x)
  obtain ⟨U⟩ := abstract_conformal_filling_gives_double_pole_end base D.point D.marking hj D.chart D.holomorphic
    D.end_mem D.centered W Y point D.height D.heightOrder D.gauss D.gaussOrder
  exact ⟨S,hm,fun d hd => transfer (he d hd),U.endChart,U.holomorphic⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.conformally_filled_actual_rhombic_marking
#print axioms TwoAxisHelicoid.published_poles_original_holomorphic_puncture
