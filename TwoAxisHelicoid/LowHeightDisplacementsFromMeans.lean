import TwoAxisHelicoid.SpatialMeanDisplacementSound
import TwoAxisHelicoid.QuarterSpatialLineOrder

namespace TwoAxisHelicoid
open Complex Set

/-- Four certified quadrature enclosures and the strict rate on the
early segment control all five endpoint inequalities in the low slab. -/
theorem low_height_displacements_of_means
    (row : CheckedQuarterSpatialLine false false false (7/32) (9/16) (1/1) (-23645/4096) (-21/2048) (-8213303/4194304) (-1373519/4194304))
    (early : CheckedHorizontalDisplacement false (7/32) (9/16) (1/1) (-2458065/2097152) (-9342639/8388608))
    (lower : CheckedHorizontalDisplacement false (3/8) (3/5) (1/1) (-22984197/16777216) (-22356879/16777216))
    (upper : CheckedHorizontalDisplacement false (1/2) (15/32) (1/1) (-25599107/16777216) (-23151839/16777216))
    (late : CheckedHorizontalDisplacement true (1/2) (3/5) (1/1) (1277165/16777216) (1580041/16777216)) :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    AntitoneOn (fun x : ℝ => X ⟨x,7/32⟩ 1) (Icc (9/16:ℝ) 1) ∧
    -(5/4:ℝ)≤X ⟨1,7/32⟩ 1-X ⟨9/16,7/32⟩ 1 ∧
    X ⟨1,3/8⟩ 1-X ⟨3/5,3/8⟩ 1< -(5/4:ℝ) ∧
    X ⟨1,1/2⟩ 1-X ⟨15/32,1/2⟩ 1< -(5/4:ℝ) ∧
    0<X ⟨1,1/2⟩ 0-X ⟨3/5,1/2⟩ 0 := by
  intro p X
  have geom := actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
    p.vertical_closed p.horizontal_closed
  have d : HasTwoAxisHelicoidCoordinateDifferential X p.t p.a 1 p.height_pos := fun z hz => (geom.2.2.2 z hz).1
  have tall := (by norm_num [rootTLower] : (1/2:ℝ)<rootTLower).trans certifiedClosedParameters_bounds.1.1
  have off {e l r : ℚ} (ep : 0<e) (elow : e≤1/2) (x : ℝ) (_ : x∈Icc (l:ℝ) r) :
      centralBandEdgePoint false e x∉certifiedPeriodPair.lattice := by
    apply rhombic_horizontal_strip_not_mem p.height_pos
    change (e:ℝ)∈Ioo (0:ℝ) p.t
    have bound : (e:ℝ)≤((1/2:ℚ):ℝ) := Rat.cast_le.mpr elow
    norm_num at bound
    exact ⟨by exact_mod_cast ep,bound.trans_lt tall⟩
  have ord := (row.primitive_order d (off (by decide +kernel) (by decide +kernel))).1 (by decide +kernel)
  have a := early.sound d (off (by decide +kernel) (by decide +kernel))
  have b := lower.sound d (off (by decide +kernel) (by decide +kernel))
  have c := upper.sound d (off (by decide +kernel) (by decide +kernel))
  have g := late.sound d (off (by decide +kernel) (by decide +kernel))
  norm_num [centralBandEdgePoint] at ord a b c g
  exact ⟨ord,by linarith [a.1],by linarith [b.2],by linarith [c.2],by linarith [g.1]⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.low_height_displacements_of_means
