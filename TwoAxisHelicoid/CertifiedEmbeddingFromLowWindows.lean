import TwoAxisHelicoid.CertifiedQuarterHeightExterior
import TwoAxisHelicoid.LowSlabGateCover
import TwoAxisHelicoid.LowHeightQuarterSimplicity
import TwoAxisHelicoid.LowSlabHeightGates
import TwoAxisHelicoid.LowSlabEarlyPointCover
import TwoAxisHelicoid.LowSlabSpatialLeftCover
import TwoAxisHelicoid.LowSlabSpatialRightCover
import TwoAxisHelicoid.PositiveHeightSpatialCriterion

namespace TwoAxisHelicoid
open Complex Set Topology

/-- Every low positive horizontal section of the actual torus
immersion is embedded, including both copies of the quarter arc and
the intersection with the vertical axis. -/
theorem low_positive_level_injective_of_windows
    (transverse :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    ∀ z : ℂ, z.re∈Ioo (0:ℝ) 1 → z.im∈Ioo (0:ℝ) p.t →
      X z 2-X 1 2∈Ioc (0:ℝ) (1/4) → X 1 1<X z 1)
    (gauss :
    let p := certifiedClosedParameters
    let H := actualComplexHeight p.t p.a 1 p.height_pos
    let G := thetaGauss p.t p.a 1
    (∀ z : ℂ, z.re∈Icc (0:ℝ) 1 → z.im∈Ioc (0:ℝ) (3/8) → 0<(H z).re → (G z).re<0) ∧
    ∀ z : ℂ, z.re∈Icc (0:ℝ) 1 → z.im∈Ioo (0:ℝ) p.t → 7/32≤z.im →
      (H z).re∈Ioc (0:ℝ) (1/4) → (G z).im<0)
    (positions :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    let P := fun z : ℂ => X z 0-X 1 0
    let Y := fun z : ℂ => X z 1-X 1 1
    (∀ x∈Icc (1/2:ℝ) 1, ∀ y∈Icc (0:ℝ) (7/32), 0≤P ⟨x,y⟩) ∧
    (∀ x∈Icc (9/16:ℝ) 1, Y ⟨x,7/32⟩≤5/4) ∧
    (∀ x∈Icc (15/32:ℝ) (3/5), ∀ y∈Icc (3/8:ℝ) (1/2), 5/4<Y ⟨x,y⟩) ∧
    ∀ x∈Icc (15/32:ℝ) (3/5), P ⟨x,1/2⟩<0) :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    ∀ h∈Ioc (0:ℝ) (1/4), InjOn certifiedTorusImmersion {q | certifiedTorusImmersion q 2=X 1 2+h} := by
  intro p X
  have geom := actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
    p.vertical_closed p.horizontal_closed
  have d : HasTwoAxisHelicoidCoordinateDifferential X p.t p.a 1 p.height_pos := fun z hz => (geom.2.2.2 z hz).1
  obtain ⟨axis,early,middle,left⟩ := low_slab_height_gates lowSlabGateCover
    (by simpa only [div_one] using lowSlabSpatialLeftCover)
    (by simpa only [div_one] using lowSlabSpatialRightCover) (by simpa only [div_one] using lowSlabEarlyPointCover)
  obtain ⟨realSign,imagSign⟩ := gauss
  obtain ⟨earlyP,earlyY,middleY,lateP⟩ := positions
  have simple := low_height_quarter_simple_from_windows axis early middle left realSign imagSign earlyP earlyY middleY lateP
  intro h hh u hu v hv same
  have side (z : ℂ) (zx : z.re∈Ioo (0:ℝ) 1) (zy : z.im∈Ioo (0:ℝ) p.t) (level : X z 2=X 1 2+h) : X 1 1<X z 1 :=
    transverse z zx zy (show X z 2-X 1 2∈Ioc (0:ℝ) (1/4) by rwa [level,add_sub_cancel_left])
  exact positive_level_injective_from_quarter p.height_pos p.abscissa_mem hh.1 d geom.1 (simple h hh) side hu hv
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.injective same)

/-- Unconditional global closed embedding of the certified period
solution. Positive heights are covered by the two explicit ranges,
negative heights by the marked half-turn, and the central fiber
includes both saddles and the infinite real axis. -/
theorem global_embedding_of_low_positive_levels
    (central :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    InjOn certifiedTorusImmersion {q | certifiedTorusImmersion q 2=X 1 2})
    (lowLevels :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    ∀ h∈Ioc (0:ℝ) (1/4), InjOn certifiedTorusImmersion {q | certifiedTorusImmersion q 2=X 1 2+h}) : IsClosedEmbedding certifiedTorusImmersion := by
  let p := certifiedClosedParameters
  let L := certifiedPeriodPair
  let X := actualGlobalImmersion p.t p.a 1 p.height_pos
  have geom := actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
    p.vertical_closed p.horizontal_closed
  have d : HasTwoAxisHelicoidCoordinateDifferential X p.t p.a 1 p.height_pos := fun z hz => (geom.2.2.2 z hz).1
  let Y := fun q : PuncturedPeriodTorus L => periodTorusLift L X geom.1 q.1
  have coord {u v : PuncturedPeriodTorus L} : certifiedTorusImmersion u=certifiedTorusImmersion v ↔ Y u=Y v :=
    ⟨fun e => (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.injective e,fun e => congrArg coordinateToEuclidean e⟩
  obtain ⟨g,q,data,global⟩ := actual_positive_height_embedding_test p.height_pos p.abscissa_mem d geom.1
  have all : Function.Injective Y := global.mpr ⟨fun _ hu _ hv eq => central hu hv (coord.mpr eq),by
    intro h
    apply (data h).2.2.2.2.mp
    rw [(data h).2.2.1]
    intro u hu v hv same
    rcases le_or_gt h.1 (1/4) with low|high
    · exact lowLevels h.1 ⟨h.2,low⟩ hu hv (coord.mpr same)
    · by_contra ne
      have bound := certified_quarter_height_exterior_embedding.2 (u,v) ⟨coord.mpr same,ne⟩
      change |Y u 2-X 1 2|<1/4 at bound
      change Y u 2=X 1 2+h.1 at hu
      rw [hu,add_sub_cancel_left,abs_of_pos h.2] at bound
      exact high.not_ge bound.le⟩
  exact IsClosedEmbedding.of_continuous_injective_isClosedMap certifiedTorusImmersion_isProperMap.continuous
    (fun _ _ eq => all (coord.mp eq)) certifiedTorusImmersion_isProperMap.isClosedMap

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.low_positive_level_injective_of_windows
#print axioms TwoAxisHelicoid.global_embedding_of_low_positive_levels
