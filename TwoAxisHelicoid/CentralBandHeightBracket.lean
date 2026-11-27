import TwoAxisHelicoid.CentralBandEdgeSound
import TwoAxisHelicoid.CentralHeightArc
import TwoAxisHelicoid.HeightEndAxisCenter

namespace TwoAxisHelicoid
open Complex Set

/-- On every row from 1/8 to 3/8, the actual central arc lies strictly
between x=1/2 and x=5/8. Only the two height edges enter this result. -/
theorem central_band_bracket_of_height_edges
    (left : CheckedCentralBandEdge .heightNeg true (1/2) (1/8) (3/8))
    (right : CheckedCentralBandEdge .heightPos true (5/8) (1/8) (3/8)) :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    ∀ y∈Icc (1/8:ℝ) (3/8), ∃! x : ℝ, x∈Ioo (1/2:ℝ) (5/8) ∧ X ((x:ℂ)+I*y) 2=X 1 2 := by
  intro p X y hy
  have ht : (3/8:ℝ)<p.t := (by norm_num [rootTLower] : (3/8:ℝ)<rootTLower).trans certifiedClosedParameters_bounds.1.1
  have yr : y∈Ioo 0 p.t := ⟨by linarith [hy.1],hy.2.trans_lt ht⟩
  have ys : y∈Icc ((1/8:ℚ):ℝ) ((3/8:ℚ):ℝ) := by norm_num; exact hy
  have d : HasTwoAxisHelicoidCoordinateDifferential X p.t p.a 1 p.height_pos := fun z hz =>
    ((actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
      p.vertical_closed p.horizontal_closed).2.2.2 z hz).1
  have per := actualGlobalImmersion_add_lattice p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0) p.vertical_closed p.horizontal_closed
  obtain ⟨x,⟨hx,eq⟩,un⟩ := actual_quarter_central_plane_unique p.height_pos p.abscissa_mem yr d per
  have reg (x : ℝ) : (x:ℂ)+I*y∉certifiedPeriodPair.lattice := rhombic_horizontal_strip_not_mem p.height_pos (by
    change ((x:ℂ)+I*y).im∈Ioo 0 p.t
    simpa using yr)
  have repr (x : ℝ) : (⟨x,y⟩:ℂ)=(x:ℂ)+I*y := by apply Complex.ext <;> simp
  have lo : X (((1/2:ℝ):ℂ)+I*y) 2<X 1 2 := by
    have v := left.sound y ys yr
    apply sub_neg.mp
    rw [actual_complex_height_centered_primitive p.height_pos d (reg _)]
    simpa [CentralBandQuantity.holds,centralBandEdgePoint,repr] using v
  have hi : X 1 2<X (((5/8:ℝ):ℂ)+I*y) 2 := by
    have v := right.sound y ys yr
    apply sub_pos.mp
    rw [actual_complex_height_centered_primitive p.height_pos d (reg _)]
    simpa [CentralBandQuantity.holds,centralBandEdgePoint,repr] using v
  have m := actual_quarter_height_row_strictMono p.height_pos yr d
  have mid := Ioo_subset_Icc_self hx
  refine ⟨x,⟨⟨(m.lt_iff_lt (by norm_num : (1/2:ℝ)∈Icc 0 1) mid).mp (lo.trans_eq eq.symm),
    (m.lt_iff_lt mid (by norm_num : (5/8:ℝ)∈Icc 0 1)).mp (eq.trans_lt hi)⟩,eq⟩,?_⟩
  intro v h
  exact un v ⟨⟨by linarith [h.1.1],by linarith [h.1.2]⟩,h.2⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.central_band_bracket_of_height_edges
