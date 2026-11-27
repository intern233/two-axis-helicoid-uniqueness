import TwoAxisHelicoid.LowSlabEarlyPosition
import TwoAxisHelicoid.QuarterSpatialLineOrder
import TwoAxisHelicoid.RectangleHarmonicSpatialBounds

namespace TwoAxisHelicoid
open Complex Set InnerProductSpace

/-- Spatial comparisons on the two early and two late windows of
the certified low levels. All displacements are anchored on the
actual infinite vertical axis. -/
theorem low_height_window_positions_of_displacements
    (quarterSpatialEarlyLeftCover : CheckedQuarterSpatialLine true false true (1/2) (0/1) (7/32) (-79397/4096) (-25/1024) (-1323469/524288) (-1464169/4194304))
    (quarterSpatialEarlyRightCover : CheckedQuarterSpatialLine true false true (1/1) (0/1) (7/32) (-4983/1024) (-263/2048) (-1907549/2097152) (-22225/131072))
    (quarterSpatialEarlyBottomCover : CheckedQuarterSpatialLine true false false (0/1) (1/2) (1/1) (-70057/4096) (-2221/4096) (-251751/65536) (-52605/131072))
    (quarterSpatialEarlyTopCover : CheckedQuarterSpatialLine true false false (7/32) (1/2) (1/1) (-1117/256) (-71/4096) (-927233/524288) (-77305/262144))
    (quarterSpatialMiddleLeftCover : CheckedQuarterSpatialLine false true true (15/32) (3/8) (1/2) (-887/512) (-1/256) (-725767/4194304) (-827/32768))
    (quarterSpatialMiddleRightCover : CheckedQuarterSpatialLine false true true (3/5) (3/8) (1/2) (4001/4096) (2551/512) (78011/524288) (127619/262144))
    (quarterSpatialMiddleBottomCover : CheckedQuarterSpatialLine false false false (3/8) (15/32) (3/5) (-6109/2048) (-9/4096) (-7525413/20971520) (-894999/20971520))
    (quarterSpatialMiddleTopCover : CheckedQuarterSpatialLine false false false (1/2) (15/32) (3/5) (43/4096) (7021/2048) (1115331/20971520) (15905211/41943040))
    (quarterSpatialLateHorizontalCover : CheckedQuarterSpatialLine true false false (1/2) (15/32) (3/5) (7/2048) (1149/256) (27363/524288) (15543339/41943040))
    (displacements :
      let p := certifiedClosedParameters
      let X := actualGlobalImmersion p.t p.a 1 p.height_pos
      AntitoneOn (fun x : ℝ => X ⟨x,7/32⟩ 1) (Icc (9/16:ℝ) 1) ∧
      -(5/4:ℝ)≤X ⟨1,7/32⟩ 1-X ⟨9/16,7/32⟩ 1 ∧
      X ⟨1,3/8⟩ 1-X ⟨3/5,3/8⟩ 1< -(5/4:ℝ) ∧
      X ⟨1,1/2⟩ 1-X ⟨15/32,1/2⟩ 1< -(5/4:ℝ) ∧
      0<X ⟨1,1/2⟩ 0-X ⟨3/5,1/2⟩ 0) :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    let P := fun z : ℂ => X z 0-X 1 0
    let Y := fun z : ℂ => X z 1-X 1 1
    (∀ x∈Icc (1/2:ℝ) 1, ∀ y∈Icc (0:ℝ) (7/32), 0≤P ⟨x,y⟩) ∧
    (∀ x∈Icc (9/16:ℝ) 1, Y ⟨x,7/32⟩≤5/4) ∧
    (∀ x∈Icc (15/32:ℝ) (3/5), ∀ y∈Icc (3/8:ℝ) (1/2), 5/4<Y ⟨x,y⟩) ∧
    ∀ x∈Icc (15/32:ℝ) (3/5), P ⟨x,1/2⟩<0 := by
  intro p X P Y
  have geom := actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
    p.vertical_closed p.horizontal_closed
  have d : HasTwoAxisHelicoidCoordinateDifferential X p.t p.a 1 p.height_pos := fun z hz => (geom.2.2.2 z hz).1
  have tall := (by norm_num [rootTLower] : (1/2:ℝ)<rootTLower).trans certifiedClosedParameters_bounds.1.1
  have off {z : ℂ} (a : 0<z.im) (b : z.im≤1/2) : z∉certifiedPeriodPair.lattice :=
    rhombic_horizontal_strip_not_mem p.height_pos ⟨a,b.trans_lt tall⟩
  have axis {y : ℝ} (pos : 0<y) (low : y≤1/2) :
      X ⟨1,y⟩ 0=X 1 0 ∧ X ⟨1,y⟩ 1=X 1 1 := by
    have ax := actual_primitive_vertical_line p.height_pos d (show y∈Ioo (-p.t) p.t from
      ⟨by linarith [p.height_pos],low.trans_lt tall⟩)
    rwa [show (1:ℂ)+I*y=⟨1,y⟩ by apply Complex.ext <;> simp] at ax
  constructor
  · have early := low_slab_early_position_from_edges
      (by intro u hu; have b := quarterSpatialEarlyLeftCover.sound.1 u (by norm_num; exact hu)
          norm_num [centralBandEdgePoint] at b; linarith [b.2])
      (by intro u hu; have b := quarterSpatialEarlyRightCover.sound.1 u (by norm_num; exact hu)
          norm_num [centralBandEdgePoint] at b; linarith [b.2])
      (by intro u hu; have b := quarterSpatialEarlyBottomCover.sound.1 u (by norm_num; exact hu)
          norm_num [centralBandEdgePoint] at b; linarith [b.2])
      (by intro u hu; have b := quarterSpatialEarlyTopCover.sound.1 u (by norm_num; exact hu)
          norm_num [centralBandEdgePoint] at b; linarith [b.2])
    exact fun x hx y hy => sub_nonneg.mpr (early x hx y hy)
  have horizontal {e l r : ℚ} (he : 0<e) (le : e≤1/2) (x : ℝ) (_ : x∈Icc (l:ℝ) r) :
      centralBandEdgePoint false e x∉certifiedPeriodPair.lattice := by
    apply off
    · change 0<(e:ℝ); exact_mod_cast he
    · change (e:ℝ)≤1/2
      simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).mpr le
  have vertical {e : ℚ} (y : ℝ) (hy : y∈Icc ((3/8:ℚ):ℝ) ((1/2:ℚ):ℝ)) :
      centralBandEdgePoint true e y∉certifiedPeriodPair.lattice := by
    apply off
    · change 0<y
      exact (by norm_num : (0:ℝ)<((3/8:ℚ):ℝ)).trans_le hy.1
    · change y≤1/2
      simpa using hy.2
  obtain ⟨ord,disp,br,tl,late⟩ := displacements
  constructor
  · change -(5/4:ℝ)≤X ⟨1,7/32⟩ 1-X ⟨9/16,7/32⟩ 1 at disp
    rw [(axis (y:=7/32) (by norm_num) (by norm_num)).2] at disp
    intro x hx
    have cap := ord (show (9/16:ℝ)∈Icc (9/16:ℝ) 1 by norm_num) hx hx.1
    change X ⟨x,7/32⟩ 1≤X ⟨9/16,7/32⟩ 1 at cap
    change X ⟨x,7/32⟩ 1-X 1 1≤5/4
    linarith
  constructor
  · have l := (quarterSpatialMiddleLeftCover.primitive_order d vertical).1 (by decide +kernel)
    have r := (quarterSpatialMiddleRightCover.primitive_order d vertical).2 (by decide +kernel)
    have b := (quarterSpatialMiddleBottomCover.primitive_order d (horizontal (by decide +kernel) (by decide +kernel))).1 (by decide +kernel)
    have t := (quarterSpatialMiddleTopCover.primitive_order d (horizontal (by decide +kernel) (by decide +kernel))).2 (by decide +kernel)
    norm_num [centralBandEdgePoint] at l r b t
    change X ⟨1,3/8⟩ 1-X ⟨3/5,3/8⟩ 1< -(5/4:ℝ) at br
    change X ⟨1,1/2⟩ 1-X ⟨15/32,1/2⟩ 1< -(5/4:ℝ) at tl
    rw [(axis (y:=3/8) (by norm_num) (by norm_num)).2] at br
    rw [(axis (y:=1/2) (by norm_num) (by norm_num)).2] at tl
    have corners : X 1 1+5/4<min (X ⟨3/5,3/8⟩ 1) (X ⟨15/32,1/2⟩ 1) := lt_min (by linarith) (by linarith)
    intro x hx y hy
    have bound := harmonic_rectangle_lower_from_corners (u:=fun z => X z 1)
      (fun z _ yy => (geom.2.2.1 z (off (by linarith [yy.1]) yy.2)).comp_CLM
        (ContinuousLinearMap.proj 1 : (Fin 3 → ℝ) →L[ℝ] ℝ)) l r b t ⟨x,y⟩ hx hy
    change 5/4<X ⟨x,y⟩ 1-X 1 1
    linarith [corners.trans_le bound]
  · change 0<X ⟨1,1/2⟩ 0-X ⟨3/5,1/2⟩ 0 at late
    have ord := (quarterSpatialLateHorizontalCover.primitive_order d (horizontal (by decide +kernel) (by decide +kernel))).2 (by decide +kernel)
    norm_num [centralBandEdgePoint] at ord
    rw [(axis (y:=1/2) (by norm_num) (by norm_num)).1] at late
    intro x hx
    have cap := ord hx (show (3/5:ℝ)∈Icc (15/32:ℝ) (3/5) by norm_num) hx.2
    change X ⟨x,1/2⟩ 0-X 1 0<0
    linarith

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.low_height_window_positions_of_displacements
