import TwoAxisHelicoid.CentralArcSpatialCriterion
import TwoAxisHelicoid.PositiveHeightSpatialCriterion
import TwoAxisHelicoid.CertifiedCentralHalfPeriods
import TwoAxisHelicoid.OriginalExistenceCompactCriterion

namespace TwoAxisHelicoid
open Complex Set MeasureTheory Topology
open scoped Interval

/-- Independent existence of an embedded genus-one model is equivalent
to tests on one central arc and weighted Gauss chords on a bounded
interval of positive physical heights. Every other horizontal
level and every possible axis contact are included in the equivalence. -/
theorem certified_height_slice_existence_criterion :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    ∃ (r : ℝ → ℝ) (g : Ioi (0:ℝ) → ℝ → ℂ) (C : ℝ), 0<C ∧
      (∀ y∈Ioo 0 p.t, r y∈Ioo (0:ℝ) 1 ∧ X ((r y:ℂ)+I*y) 2=X 1 2) ∧
      ContinuousOn r (Ioo 0 p.t) ∧ (∀ h, Continuous (g h)) ∧
      (Nonempty OriginalHelicoidRepresentative ↔
        InjOn (fun y : ℝ => X ((r y:ℂ)+I*y)) (Ioo 0 p.t) ∧
        (∀ y∈Ioo 0 p.t, X 1 1<X ((r y:ℂ)+I*y) 1) ∧
        ∀ h : Ioi (0:ℝ), h.1≤C → ∀ u v, u<v → (∫ y in u..v,horizontalWeightedGauss p.t p.a (g h) y)≠0) := by
  intro p X
  let L := rhombicPeriodPair p.t p.height_pos
  have d : HasTwoAxisHelicoidCoordinateDifferential X p.t p.a 1 p.height_pos := fun z hz =>
    ((actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
      p.vertical_closed p.horizontal_closed).2.2.2 z hz).1
  have per := actualGlobalImmersion_add_lattice p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
    p.vertical_closed p.horizontal_closed
  let Y := fun u : PuncturedPeriodTorus L => periodTorusLift L X per u.1
  have mark := certified_central_half_periods_separated.1
  change 1/2<X ((1+I*p.t)/2) 1-X 1 1 at mark
  obtain ⟨r,inside,cont,_,_,lev,central⟩ := actual_central_spatial_embedding_test p.height_pos p.abscissa_mem d per (by linarith)
  obtain ⟨g,q,data,global⟩ := actual_positive_height_embedding_test p.height_pos p.abscissa_mem d per
  obtain ⟨_,K,kc,sat,_⟩ := certified_compact_embedding_criterion
  have cy : Continuous Y := periodTorusLift_continuous_punctured L X per (fun z hz => (d z hz).continuousAt)
  have cv : Continuous (fun u => Y u 2-X 1 2) := ((continuous_apply 2).comp cy).sub continuous_const
  obtain ⟨b,hb⟩ := (kc.image cv).bddAbove
  let C := max b 1
  have eqY {u v : PuncturedPeriodTorus L} : certifiedTorusImmersion u=certifiedTorusImmersion v ↔ Y u=Y v := by
    constructor
    · exact fun h => (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.injective h
    · exact fun h => congrArg coordinateToEuclidean h
  have existence : Nonempty OriginalHelicoidRepresentative ↔ Function.Injective Y := by
    constructor
    · rintro ⟨s⟩ u v e
      apply (pointed_original_embedding_and_similarity s.toOriginalSmoothHelicoid (original_graph_poles_cap_and_index s).2.2.1).1.injective
      exact eqY.mpr e
    · intro hi
      obtain ⟨s,_⟩ := certified_original_representative_of_injective (fun _ _ e => hi (eqY.mp e))
      exact ⟨s⟩
  have far {h : Ioi (0:ℝ)} (above : C<h.1) : InjOn Y (range (q h)) := by
    intro u hu v _ e
    by_contra ne
    have k := (sat (show (u,v)∈immersionDoublePoints certifiedTorusImmersion from ⟨eqY.mpr e,ne⟩)).1
    have bound := hb (mem_image_of_mem (fun w => Y w 2-X 1 2) k)
    rw [(data h).2.2.1] at hu
    change Y u 2=X 1 2+h.1 at hu
    change Y u 2-X 1 2≤b at bound
    have cb : b≤C := le_max_left _ _
    linarith
  refine ⟨r,g,C,zero_lt_one.trans_le (le_max_right _ _),fun y hy => ⟨inside y hy,lev y hy⟩,cont,fun h => (data h).1,?_⟩
  rw [existence,global,central]
  constructor
  · rintro ⟨⟨simple,above⟩,nonzero⟩
    exact ⟨simple,above,fun h _ => nonzero h⟩
  · rintro ⟨simple,above,tests⟩
    refine ⟨⟨simple,above⟩,fun h => ?_⟩
    rcases le_or_gt h.1 C with hc|hc
    · exact tests h hc
    · exact (data h).2.2.2.2.mp (far hc)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_height_slice_existence_criterion
