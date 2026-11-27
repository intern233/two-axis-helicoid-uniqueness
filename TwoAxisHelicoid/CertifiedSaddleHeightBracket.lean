import TwoAxisHelicoid.CentralArcHeightBracket
import TwoAxisHelicoid.CentralBandEdgeSound
import TwoAxisHelicoid.CentralBandLeftHeightCover
import TwoAxisHelicoid.CentralArcLeftEarlyCover
import TwoAxisHelicoid.CentralArcLeftLateCover
import TwoAxisHelicoid.CentralArcSaddleThirdCover
import TwoAxisHelicoid.CentralArcSaddleSlopeCover
import TwoAxisHelicoid.CentralHeightArc
import TwoAxisHelicoid.HeightEndAxisCenter

namespace TwoAxisHelicoid
open Complex Set

/-- Every row between the saddle and the central half-period meets the
physical central level at exactly one abscissa strictly between 1/2
and the saddle abscissa. The right boundary height is strictly increasing. -/
theorem certified_saddle_height_bracket :
    let p := certifiedClosedParameters
    let H := actualComplexHeight p.t p.a 1 p.height_pos
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    let Z := fun x y : ℝ => (x:ℂ)+I*y
    (H ((1+I*p.t)/2)).re=0 ∧ StrictMonoOn (fun y => (H (Z p.a y)).re) (Icc 0 (p.t/2)) ∧
      ∀ y∈Ioo 0 (p.t/2), ∃! x : ℝ, x∈Ioo (1/2:ℝ) p.a ∧ X (Z x y) 2=X 1 2 := by
  intro p H X Z
  have d : HasTwoAxisHelicoidCoordinateDifferential X p.t p.a 1 p.height_pos := fun z hz =>
    ((actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
      p.vertical_closed p.horizontal_closed).2.2.2 z hz).1
  have per := actualGlobalImmersion_add_lattice p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
    p.vertical_closed p.horizontal_closed
  have off (x y : ℝ) (hy : y∈Ioo 0 p.t) : Z x y∉certifiedPeriodPair.lattice :=
    rhombic_horizontal_strip_not_mem p.height_pos (by change (Z x y).im∈Ioo 0 p.t; simpa [Z] using hy)
  have val (x y : ℝ) (hy : y∈Ioo 0 p.t) :
      X (Z x y) 2-X 1 2=(H (Z x y)).re := actual_complex_height_centered_primitive p.height_pos d (off _ _ hy)
  obtain ⟨r,arc,_,_,_,_,half⟩ := actual_central_height_arc p.height_pos p.abscissa_mem d per
  have mt : p.t/2∈Ioo 0 p.t := ⟨half_pos p.height_pos,half_lt_self p.height_pos⟩
  have axis := ((arc _ mt).2 _ (arc _ mt).1).mpr rfl
  rw [half] at axis
  have mid : (H (Z (1/2) (p.t/2))).re=0 := by rw [← val _ _ mt,axis,sub_self]
  obtain ⟨tb,ab⟩ := certifiedClosedParameters_bounds
  have large : (3/8:ℝ)<p.t := (by norm_num [rootTLower] : (3/8:ℝ)<rootTLower).trans tb.1
  have middle (y : ℝ) (hy : y∈Icc (1/8:ℝ) (3/8)) : (H (Z (1/2) y)).re<0 := by
    have b := centralBandLeftHeightCover.sound y (by norm_num; exact hy)
      (by change y∈Ioo 0 p.t; exact ⟨(by norm_num : (0:ℝ)<1/8).trans_le hy.1,hy.2.trans_lt large⟩)
    have rep : Z (1/2) y=⟨(1/2:ℝ),y⟩ := by apply Complex.ext <;> simp [Z]
    rw [rep]
    simpa [CentralBandQuantity.holds,centralBandEdgePoint,H,p] using b
  obtain ⟨inc,edges⟩ := central_arc_height_boundary_signs (Ioo_subset_Icc_self tb) (Ioo_subset_Icc_self ab)
    p.height_pos p.abscissa_mem p.vertical_closed (by simpa only [div_one] using centralArcLeftEarlyCover)
    centralArcLeftLateCover (by simpa only [div_one] using centralArcSaddleThirdCover)
    centralArcSaddleSlopeCover mid middle
  have eq : Z (1/2) (p.t/2)=(1+I*p.t)/2 := by dsimp [Z]; push_cast; ring
  refine ⟨eq ▸ mid,inc,?_⟩
  intro y hy
  have yt : y∈Ioo 0 p.t := ⟨hy.1,hy.2.trans mt.2⟩
  have unique := arc y yt
  have hit := (unique.2 _ unique.1).mpr rfl
  have l : X (Z (1/2) y) 2<X 1 2 := sub_neg.mp ((val _ _ yt).trans_lt (edges _ hy).1)
  have u : X 1 2<X (Z p.a y) 2 := sub_pos.mp ((val _ _ yt).symm ▸ (edges _ hy).2)
  have order := actual_quarter_height_row_strictMono p.height_pos yt d
  have ry := Ioo_subset_Icc_self unique.1
  have left := (order.lt_iff_lt (by norm_num : (1/2:ℝ)∈Icc 0 1) ry).mp (l.trans_eq hit.symm)
  have right := (order.lt_iff_lt ry (Ioo_subset_Icc_self p.abscissa_mem)).mp (hit.trans_lt u)
  refine ⟨r y,⟨⟨left,right⟩,hit⟩,fun x h => (unique.2 _ ⟨?_,h.1.2.trans p.abscissa_mem.2⟩).mp h.2⟩
  exact (by norm_num : (0:ℝ)<1/2).trans h.1.1

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_saddle_height_bracket
