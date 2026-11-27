import TwoAxisHelicoid.ObliqueThetaTile
import TwoAxisHelicoid.ObliqueThetaLevelProjection
import TwoAxisHelicoid.ObliqueThetaPosLeftCover
import TwoAxisHelicoid.ObliqueThetaPosRightCover
import TwoAxisHelicoid.ObliqueThetaPosBottomCover
import TwoAxisHelicoid.ObliqueThetaPosTopCover
import TwoAxisHelicoid.ObliqueThetaPosHeightLeftCover
import TwoAxisHelicoid.ObliqueThetaPosHeightRightCover
import TwoAxisHelicoid.ObliqueThetaNegLeftCover
import TwoAxisHelicoid.ObliqueThetaNegRightCover
import TwoAxisHelicoid.ObliqueThetaNegBottomCover
import TwoAxisHelicoid.ObliqueThetaNegTopCover
import TwoAxisHelicoid.ObliqueThetaNegHeightCover
import TwoAxisHelicoid.CertifiedCompactDoublePoints

namespace TwoAxisHelicoid
open Complex Set Topology

/-- The eleven certified boundaries imply the signed oblique inequalities
throughout the centered fundamental tile. -/
theorem certified_oblique_theta_tile :
    let p := certifiedClosedParameters
    ∀ x∈Icc (0:ℝ) 1, ∀ y∈Icc 0 (p.t/2), let z : ℂ := ⟨x,y⟩
      (1/4≤(actualComplexHeight p.t p.a 1 p.height_pos z).re →
        (obliqueThetaFactor true*centralPhaseThetaRatio p.t p.a z).re<0) ∧
      ((actualComplexHeight p.t p.a 1 p.height_pos z).re≤ -(1/4) →
        (obliqueThetaFactor false*centralPhaseThetaRatio p.t p.a z).re<0) :=
  oblique_theta_tile_from_edges
    (by simpa only [div_one] using obliqueThetaPosLeftCover) (by simpa only [div_one] using obliqueThetaPosRightCover)
    (by simpa only [div_one] using obliqueThetaPosBottomCover) (by simpa only [div_one] using obliqueThetaPosTopCover)
    (by simpa only [div_one] using obliqueThetaPosHeightLeftCover) (by simpa only [div_one] using obliqueThetaPosHeightRightCover)
    (by simpa only [div_one] using obliqueThetaNegLeftCover) (by simpa only [div_one] using obliqueThetaNegRightCover)
    (by simpa only [div_one] using obliqueThetaNegBottomCover) (by simpa only [div_one] using obliqueThetaNegTopCover)
    (by simpa only [div_one] using obliqueThetaNegHeightCover)

/-- The entire certified immersion outside the open central slab of
relative height one quarter is a closed embedding. Both boundary
planes are included. -/
theorem certified_quarter_height_exterior_embedding :
    let p := certifiedClosedParameters
    let s := actualGlobalImmersion p.t p.a 1 p.height_pos 1 2
    let K := {q | 1/4≤|certifiedTorusImmersion q 2-s|}
    IsClosedEmbedding (fun q : K => certifiedTorusImmersion q.1) ∧
      ∀ pair∈immersionDoublePoints certifiedTorusImmersion, |certifiedTorusImmersion pair.1 2-s|<1/4 := by
  intro p s K
  let X := actualGlobalImmersion p.t p.a 1 p.height_pos
  let L := certifiedPeriodPair
  have d : HasTwoAxisHelicoidCoordinateDifferential X p.t p.a 1 p.height_pos := fun z hz =>
    ((actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
      p.vertical_closed p.horizontal_closed).2.2.2 z hz).1
  have per := actualGlobalImmersion_add_lattice p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
    p.vertical_closed p.horizontal_closed
  let Y := fun q : PuncturedPeriodTorus L => periodTorusLift L X per q.1
  have simple := oblique_torus_level_injectivity p.height_pos p.abscissa_mem p.vertical_closed d per certified_oblique_theta_tile
  have outside {u v : PuncturedPeriodTorus L} (hu : u∈K) (same : certifiedTorusImmersion u=certifiedTorusImmersion v) : u=v := by
    have eq : Y u=Y v := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.injective same
    let h := Y u 2-s
    have level : Y u 2=X 1 2+h := by change Y u 2=s+(Y u 2-s); ring
    exact simple h hu level (by change Y v 2=_; rwa [← eq]) eq
  have proper := certifiedTorusImmersion_isProperMap
  have c : Continuous (fun q => |certifiedTorusImmersion q 2-s|) :=
    (((PiLp.continuous_apply (p:=2) (β:=fun _ : Fin 3 => ℝ) 2).comp proper.continuous).sub continuous_const).abs
  have closed : IsClosed K := isClosed_le continuous_const c
  refine ⟨IsClosedEmbedding.of_continuous_injective_isClosedMap (proper.continuous.comp continuous_subtype_val)
    (fun u _ eq => Subtype.ext (outside u.2 eq)) (proper.isClosedMap.comp closed.isClosedEmbedding_subtypeVal.isClosedMap),?_⟩
  rintro ⟨u,v⟩ pair
  exact lt_of_not_ge (fun high => pair.2 (outside high pair.1))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_oblique_theta_tile
#print axioms TwoAxisHelicoid.certified_quarter_height_exterior_embedding
