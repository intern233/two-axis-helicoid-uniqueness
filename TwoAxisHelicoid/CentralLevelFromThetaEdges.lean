import TwoAxisHelicoid.CentralHalfGaussCriterion
import TwoAxisHelicoid.CentralSaddleGaussQuadrant
import TwoAxisHelicoid.CertifiedSaddleHeightBracket
import TwoAxisHelicoid.CertifiedCentralHalfPeriods

namespace TwoAxisHelicoid
open Complex Set

theorem certified_central_level_from_theta_edges
    (left : CheckedCentralRatioJets false true (1/2) 0 (7/16))
    (right : CheckedCentralRatioJets false true (3/5) 0 (7/16))
    (bottom : CheckedCentralRatioJets false false 0 (1/2) (3/5))
    (top : CheckedCentralRatioJets false false (7/16) (1/2) (3/5))
    (third : CheckedCentralRatioJets true true (1/2) 0 (7/16)) :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    InjOn certifiedTorusImmersion {q | certifiedTorusImmersion q 2=X 1 2} := by
  intro p X
  let Z := fun x y : ℝ => (x:ℂ)+I*y
  have d : HasTwoAxisHelicoidCoordinateDifferential X p.t p.a 1 p.height_pos := fun z hz =>
    ((actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
      p.vertical_closed p.horizontal_closed).2.2.2 z hz).1
  have per := actualGlobalImmersion_add_lattice p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0) p.vertical_closed p.horizontal_closed
  have mark := certified_central_half_periods_separated.1
  change 1/2<X ((1+I*p.t)/2) 1-X 1 1 at mark
  obtain ⟨tb,ab⟩ := certifiedClosedParameters_bounds
  obtain ⟨mid,_,bracket⟩ := certified_saddle_height_bracket
  have quadrant := central_saddle_gauss_quadrant (Ioo_subset_Icc_self tb) (Ioo_subset_Icc_self ab) p.height_pos p.abscissa_mem
    p.vertical_closed mid left right bottom top third
  have simple := central_level_injective_of_gauss_quadrant p.height_pos p.abscissa_mem d per (by linarith) (by
    intro y hy x hx same
    obtain ⟨u,⟨bu,hu⟩,_⟩ := bracket y hy
    have uy : y∈Ioo 0 p.t := ⟨hy.1,hy.2.trans (half_lt_self p.height_pos)⟩
    have un := (actual_quarter_height_row_strictMono p.height_pos uy d).injOn (Ioo_subset_Icc_self hx)
      (show u∈Icc (0:ℝ) 1 from ⟨by linarith [bu.1],by linarith [bu.2,p.abscissa_mem.2]⟩) (same.trans hu.symm)
    have off : Z x y∉certifiedPeriodPair.lattice := rhombic_horizontal_strip_not_mem p.height_pos
      (by change (Z x y).im∈Ioo 0 p.t; simpa [Z] using uy)
    exact (quadrant x ⟨un ▸ bu.1,(un ▸ bu.2).le⟩ y ⟨hy.1,hy.2.le⟩).2.2 (by
      rw [← actual_complex_height_centered_primitive p.height_pos d off,same,sub_self]))
  intro u hu v hv eq
  exact simple hu hv ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.injective eq)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_central_level_from_theta_edges
