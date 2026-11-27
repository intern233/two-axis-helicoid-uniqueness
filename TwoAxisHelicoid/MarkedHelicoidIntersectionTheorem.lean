import TwoAxisHelicoid.RhombicCellComparison
import TwoAxisHelicoid.HoffmanWhiteWindingReduction
import TwoAxisHelicoid.TwoAxisComponentSides

namespace TwoAxisHelicoid
open Complex Set Topology

private theorem vertical_half_turn_on_helicoid {α b : ℝ} {p : Fin 3 → ℝ}
    (on : p∈range (axisRuledHelicoid I α b)) : (![-p 0,-p 1,p 2] : Fin 3 → ℝ)∈range (axisRuledHelicoid I α b) := by
  obtain ⟨⟨r,v⟩,rfl⟩ := on
  refine ⟨⟨-r,v⟩,?_⟩
  rw [axisRuledHelicoid_ruling,axisRuledHelicoid_ruling]
  ext j
  fin_cases j <;> simp

/-- The exact-intersection conclusion used in the integer winding
reduction follows from the marked geometric hypotheses. The actual
torus is tested throughout its compact core and on its end. -/
theorem marked_rhombic_helicoid_intersection : RhombicHelicoidIntersectionPrinciple := by
  intro t ht X hX α hα b F A H hE horizontal vertical endGraph calibrated
  let L := rhombicPeriodPair t ht
  let S := range (axisRuledHelicoid I α b)
  let V := fun p : Fin 3 → ℝ => ![-p 0,-p 1,p 2]
  have eqH := inverse_image_standardHelicoid_axisNormalization hα b
  have align : S=range (axisRuledHelicoid I α 0) := eqH.symm.trans calibrated
  have avoid := marked_first_cell_avoids_helicoid ht hα hX hE b vertical endGraph align
  have swapped := two_axis_component_half_turn ht hX
  have avoid_other {w : ℂ} (hw : w∈rhombicAxisRectangle (-2) t) (on : X w∈S) : False := by
    have hv : V (X w) ∈ V '' (X '' rhombicAxisRectangle (-2) t) := ⟨X w,⟨w,hw,rfl⟩,rfl⟩
    rw [show V '' (X '' rhombicAxisRectangle (-2) t)=X '' rhombicAxisRectangle (-1) t from swapped] at hv
    obtain ⟨v,member,eq⟩ := hv
    exact avoid _ member (eq.symm ▸ vertical_half_turn_on_helicoid on)
  change range (harmonicTorusImmersion hX) ∩ ((axisSpatialNormalization hα ![0,0,b]) ⁻¹' range (fun w : ℂ => standardHelicoid w.re w.im)) = _
  rw [eqH]
  ext p
  constructor
  · rintro ⟨inX,on⟩
    rw [harmonicTorusImmersion_range hX] at inX
    obtain ⟨z,hz,rfl⟩ := inX
    by_contra noaxes
    change ¬ ((X z 1=0 ∧ X z 2=0) ∨ X z 0=0 ∧ X z 1=0) at noaxes
    have axes := rhombic_physical_axes_preimages ht hX hE.injective hz
    have off : rhombicHorizontalReflection ht (periodTorusProjection L z)≠periodTorusProjection L z ∧
        rhombicVerticalReflection ht (periodTorusProjection L z)≠periodTorusProjection L z := by
      exact ⟨fun e => noaxes (Or.inl (axes.2.mpr ((rhombic_horizontal_fixed_projection_height ht z).mp e))),
        fun e => noaxes (Or.inr (axes.1.mpr ((rhombic_vertical_fixed_projection_iff ht z).mp e)))⟩
    rcases (rhombic_off_axes_iff_rectangle ht _).mp off with ⟨w,hw,eq⟩ | ⟨w,hw,eq⟩
    · have image := (marked_torus_spatial_eq_iff_projection_eq hX hE.injective (rhombic_horizontal_strip_not_mem ht hw.2) hz).mpr eq
      exact avoid_other hw (image.symm ▸ on)
    · have image := (marked_torus_spatial_eq_iff_projection_eq hX hE.injective (rhombic_horizontal_strip_not_mem ht hw.2) hz).mpr eq
      exact avoid _ hw (image.symm ▸ on)
  · rintro (h | v)
    · have e : p=![p 0,0,0] := by ext j; fin_cases j <;> simp [h.1,h.2]
      exact ⟨e.symm ▸ horizontal _,(relative_horizontal_im_eq_zero_iff α b _).mp ((aligned_relative_horizontal_at_height_zero align _ h.2).mpr h.1)⟩
    · have e : p=![0,0,p 2] := by ext j; fin_cases j <;> simp [v.1,v.2]
      have zero := (helicoidRelativeHorizontal_eq_zero_iff α b p).mpr v
      exact ⟨e.symm ▸ vertical _,(relative_horizontal_im_eq_zero_iff α b _).mp (congrArg im zero)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_rhombic_helicoid_intersection
