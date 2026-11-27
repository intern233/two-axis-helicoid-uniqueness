import TwoAxisHelicoid.MarkedHelicoidGaussPole
import TwoAxisHelicoid.SchwarzNormalizedImmersion
import TwoAxisHelicoid.ScaledTorusImmersion
import TwoAxisHelicoid.TorusEndScalingOrders
import TwoAxisHelicoid.HelicoidEndReparameterization

namespace TwoAxisHelicoid
open Complex Set Filter Topology InnerProductSpace
open scoped Topology

/-- Removing the lattice values of the coefficients preserves both
germs and their meromorphic orders at the marked puncture. -/
theorem punctured_immersion_end_orders (L : PeriodPair) (X : ℂ → Fin 3 → ℝ) :
    let p := puncturedImmersionCoefficient L X
    meromorphicOrderAt (fun w => p w 2) 0=meromorphicOrderAt (fun w => immersionComplexCoefficient X w 2) 0 ∧
    meromorphicOrderAt (logDeriv (fun w => nullGauss (p w))) 0=meromorphicOrderAt (immersionGaussLogDerivative X) 0 := by
  let p := puncturedImmersionCoefficient L X
  have ev : p =ᶠ[𝓝[≠] (0:ℂ)] immersionComplexCoefficient X :=
    (punctured_lattice_regular_near_zero L).mono fun _ hw => puncturedImmersionCoefficient_eq hw
  exact ⟨meromorphicOrderAt_congr (ev.mono fun _ hw => congrFun hw 2),
    meromorphicOrderAt_congr (logDeriv_congr_nhdsNE (ev.mono fun _ hw => congrArg nullGauss hw))⟩

/-- The physically determined end orders hold in the original lattice
coordinate even if the supplied complex period basis has arbitrary
shape and scale. -/
theorem marked_straight_graph_intrinsic_end_orders (L : PeriodPair) (X : PeriodTorus L → Fin 3 → ℝ)
    (closed : IsClosedEmbedding (fun q : PuncturedPeriodTorus L => X q.1))
    (hor : ∀ r : ℝ, (![r,0,0] : Fin 3 → ℝ)∈range (fun q : PuncturedPeriodTorus L => X q.1))
    (ver : ∀ r : ℝ, (![0,0,r] : Fin 3 → ℝ)∈range (fun q : PuncturedPeriodTorus L => X q.1))
    (regular : ∀ z∉L.lattice, (∀ j, HarmonicAt (fun w => X (periodTorusProjection L w) j) z) ∧
      ConformalCoordinateDerivatives (X ∘ periodTorusProjection L) z ∧ Function.Injective (fderiv ℝ (X ∘ periodTorusProjection L) z))
    (graph : HasHelicoidC1End (fun q : PuncturedPeriodTorus L => coordinateToTube (X q.1))) :
    meromorphicOrderAt (fun w => immersionComplexCoefficient (X ∘ periodTorusProjection L) w 2) 0=(-2:ℤ) ∧
    meromorphicOrderAt (immersionGaussLogDerivative (X ∘ periodTorusProjection L)) 0=(-2:ℤ) := by
  obtain ⟨s,t,hs,ht,hp,imm⟩ := straight_axes_to_two_axis_harmonic_immersion L X closed hor ver regular
  let M := rhombicPeriodPair t ht
  let Y := fun z : ℂ => X (periodTorusProjection L (s⁻¹*z))
  obtain ⟨e,he⟩ := scaled_harmonic_quotient_correspondence L M s hs hp X imm
  have eq : (fun q : PuncturedPeriodTorus L => X q.1) ∘ e.symm=harmonicTorusImmersion imm := by
    funext q
    simpa only [e.apply_symm_apply,Function.comp_apply] using (he (e.symm q)).symm
  have hg : HasHelicoidC1End (coordinateToTube ∘ harmonicTorusImmersion imm) := by
    rw [← eq]
    exact graph.comp_homeomorph e.symm
  have cl : IsClosedEmbedding (harmonicTorusImmersion imm) := eq ▸ closed.comp e.symm.isClosedEmbedding
  obtain ⟨hh,gg⟩ := marked_helicoid_two_double_poles ht imm cl.isProperMap hg
  obtain ⟨eh,eg⟩ := punctured_immersion_end_orders M Y
  have back := marked_torus_scaled_end_orders M L Y s hs (fun z hz => ⟨imm.harmonic z hz,imm.conformal z hz⟩)
    (eh.symm.trans hh.2) (eg.symm.trans gg.2)
  have comp : (fun w => Y (s*w))=X ∘ periodTorusProjection L := by
    funext w
    simp [Y,hs]
  change meromorphicOrderAt (fun w => puncturedImmersionCoefficient L (fun z => Y (s*z)) w 2) 0=_ ∧
    meromorphicOrderAt (logDeriv (fun w => nullGauss (puncturedImmersionCoefficient L (fun z => Y (s*z)) w))) 0=_ at back
  rw [comp] at back
  obtain ⟨h,g⟩ := punctured_immersion_end_orders L (X ∘ periodTorusProjection L)
  exact ⟨h.symm.trans back.1,g.symm.trans back.2⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_straight_graph_intrinsic_end_orders
