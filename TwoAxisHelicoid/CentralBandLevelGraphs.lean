import TwoAxisHelicoid.QuarterRowSpatialVelocity
import TwoAxisHelicoid.ActualQuarterHeightSlices

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
set_option maxHeartbeats 1200000

/-- Uniform signs on the two vertical edges and a Gauss quadrant
throughout a rectangle give an open band of physical levels whose
two horizontal coordinates are strictly monotone. This also proves
joint spatial injectivity on the whole part of the rectangle in the
height band. -/
theorem quarter_rectangle_embedded_height_band {t a L R B T : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    (lx : 0<L) (lr : L<R) (rx : R<1) (by0 : 0<B) (bt : B<T) (ty : T<t)
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht) :
    let H := actualComplexHeight t a 1 ht
    let G := thetaGauss t a 1
    let Z := fun x y : ℝ => (x:ℂ)+I*y
    let J := Icc B T
    (∀ y∈J, (H (Z L y)).re<0 ∧ 0<(H (Z R y)).re) →
    (∀ x∈Icc L R, ∀ y∈J, (G (Z x y)).re<0 ∧ (G (Z x y)).im<0) →
    ∃ ε : ℝ, 0<ε ∧
      (∀ s : ℝ, |s|<ε → ∃ r : ℝ → ℝ, ContinuousOn r J ∧
        (∀ y∈J, r y∈Ioo L R ∧ (H (Z (r y) y)).re=s) ∧
        StrictAntiOn (fun y => X (Z (r y) y) 0) J ∧ StrictMonoOn (fun y => X (Z (r y) y) 1) J) ∧
      InjOn X {z | z.re∈Icc L R ∧ z.im∈J ∧ |(H z).re|<ε} := by
  classical
  intro H G Z J edges quadrant
  let C := Icc L R
  let F := fun x y => (H (Z x y)).re
  have yR {y : ℝ} (hy : y∈J) : y∈Ioo 0 t := ⟨by0.trans_le hy.1,hy.2.trans_lt ty⟩
  have xR {x : ℝ} (hx : x∈C) : x∈Ioo (0:ℝ) 1 := ⟨lx.trans_le hx.1,hx.2.trans_lt rx⟩
  have off (x : ℝ) {y : ℝ} (hy : y∈J) : Z x y∉(rhombicPeriodPair t ht).lattice :=
    rhombic_horizontal_strip_not_mem ht (by change (Z x y).im∈Ioo 0 t; simpa [Z] using yR hy)
  have zval (x : ℝ) {y : ℝ} (hy : y∈J) : F x y=X (Z x y) 2-X 1 2 :=
    (actual_complex_height_centered_primitive ht d (off x hy)).symm
  have row (y : ℝ) (hy : y∈J) : StrictMonoOn (fun x => F x y) C := by
    intro x hx u hu e
    change F x y<F u y
    rw [zval x hy,zval u hy]
    exact sub_lt_sub_right (actual_quarter_height_row_strictMono ht (yR hy) d
      (Ioo_subset_Icc_self (xR hx)) (Ioo_subset_Icc_self (xR hu)) e) _
  have cY (x : ℝ) (y : ℝ) (hy : y∈J) : ContinuousAt (F x) y := by
    have line : Continuous (Z x) := by dsimp [Z]; fun_prop
    exact continuous_re.continuousAt.comp ((actualComplexHeight_hasDerivAt (a:=a) (c:=1) ht (off x hy)).continuousAt.comp line.continuousAt)
  have ne : J.Nonempty := ⟨B,left_mem_Icc.mpr bt.le⟩
  obtain ⟨l,hl,maxL⟩ := isCompact_Icc.exists_isMaxOn ne (fun y hy => (cY L y hy).continuousWithinAt)
  obtain ⟨u,hu,minR⟩ := isCompact_Icc.exists_isMinOn ne (fun y hy => (cY R y hy).continuousWithinAt)
  let ε := min (-(F L l)) (F R u)
  have ep : 0<ε := lt_min (neg_pos.mpr (edges l hl).1) (edges u hu).2
  have graphs (s : ℝ) (hs : |s|<ε) : ∃ r : ℝ → ℝ, ContinuousOn r J ∧
      (∀ y∈J, r y∈Ioo L R ∧ F (r y) y=s) ∧
      StrictAntiOn (fun y => X (Z (r y) y) 0) J ∧ StrictMonoOn (fun y => X (Z (r y) y) 1) J := by
    have one (y : ℝ) (hy : y∈J) : ∃ x∈Ioo L R, F x y=s := by
      obtain ⟨slo,shi⟩ := abs_lt.mp hs
      have bound : ε≤ -(F L l) := min_le_left _ _
      have atLeft : F L l ≤ -ε := by linarith only [bound]
      have left : F L y<s := (maxL hy).trans_lt (atLeft.trans_lt slo)
      have right : s<F R y := shi.trans_le ((min_le_right _ _).trans (minR hy))
      have con : ContinuousOn (fun x => F x y) C := by
        intro x _
        have line : Continuous (fun x => Z x y) := by dsimp [Z]; fun_prop
        have atX := (actualComplexHeight_hasDerivAt (a:=a) (c:=1) ht (off x hy)).continuousAt.comp
          (f:=fun u => Z u y) (line.continuousAt (x:=x))
        exact (continuous_re.continuousAt.comp atX).continuousWithinAt
      obtain ⟨x,hx,e⟩ := (intermediate_value_Icc lr.le con) (show s∈Icc (F L y) (F R y) from ⟨left.le,right.le⟩)
      exact ⟨x,⟨lt_of_le_of_ne hx.1 (fun k => left.ne (k.symm ▸ e)),lt_of_le_of_ne hx.2 (fun k => right.ne (k ▸ e.symm))⟩,e⟩
    let r := fun y => if hy : y∈J then (one y hy).choose else 0
    have spec (y : ℝ) (hy : y∈J) : r y∈Ioo L R ∧ F (r y) y=s := by
      simpa only [r,dite_eq_left hy] using (one y hy).choose_spec
    have cr : ContinuousOn r J := by
      intro y hy
      apply tendsto_order.mpr
      constructor
      · intro b low
        obtain ⟨x,bx,xy⟩ := exists_between (max_lt low (spec y hy).1.1)
        have xc : x∈C := ⟨((le_max_right _ _).trans_lt bx).le,(xy.trans (spec y hy).1.2).le⟩
        have v : F x y<s := ((row y hy) xc (Ioo_subset_Icc_self (spec y hy).1) xy).trans_eq (spec y hy).2
        filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds ((cY x y hy).eventually (Iio_mem_nhds v))] with z hz h
        exact ((le_max_left _ _).trans_lt bx).trans (((row z hz).lt_iff_lt xc (Ioo_subset_Icc_self (spec z hz).1)).mp (h.trans_eq (spec z hz).2.symm))
      · intro b high
        obtain ⟨x,yx,xb⟩ := exists_between (lt_min high (spec y hy).1.2)
        have xc : x∈C := ⟨((spec y hy).1.1.trans yx).le,(xb.trans_le (min_le_right _ _)).le⟩
        have v : s<F x y := (spec y hy).2.symm.trans_lt ((row y hy) (Ioo_subset_Icc_self (spec y hy).1) xc yx)
        filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds ((cY x y hy).eventually (Ioi_mem_nhds v))] with z hz h
        exact (((row z hz).lt_iff_lt (Ioo_subset_Icc_self (spec z hz).1) xc).mp ((spec z hz).2.trans_lt h)).trans (xb.trans_le (min_le_left _ _))
    let W := fun y => Z (r y) y
    have con (j : Fin 3) : ContinuousOn (fun y => X (W y) j) J := by
      intro y hy
      have cw : ContinuousWithinAt W J y := (continuous_ofReal.continuousAt.comp_continuousWithinAt (cr y hy)).add
        (continuous_const.mul continuous_ofReal).continuousAt.continuousWithinAt
      exact (continuous_apply j).continuousAt.comp_continuousWithinAt ((d (W y) (off (r y) hy)).continuousAt.comp_continuousWithinAt (f:=W) cw)
    have speeds (y : ℝ) (hy : y∈interior J) : deriv (fun v => X (W v) 0) y<0 ∧ 0<deriv (fun v => X (W v) 1) y := by
      have h := interior_subset hy
      have near : J∈𝓝 y := mem_interior_iff_mem_nhds.mp hy
      obtain ⟨k,kp,vel⟩ := quarter_row_spatial_velocity ht ha d ((cr y h).continuousAt near) (yR h)
        (xR (Ioo_subset_Icc_self (spec y h).1)) (s:=s) (by filter_upwards [near] with v hv using (spec v hv).2)
      obtain ⟨gr,gi⟩ := quadrant _ (Ioo_subset_Icc_self (spec y h).1) y h
      have dx : deriv (fun v => X (W v) 0) y=k*(G (W y)).im := (hasDerivAt_pi.mp vel 0).deriv
      have dy : deriv (fun v => X (W v) 1) y= -k*(G (W y)).re := (hasDerivAt_pi.mp vel 1).deriv
      rw [dx,dy]
      exact ⟨mul_neg_of_pos_of_neg kp gi,mul_pos_of_neg_of_neg (neg_lt_zero.mpr kp) gr⟩
    exact ⟨r,cr,spec,strictAntiOn_of_deriv_neg (convex_Icc _ _) (con 0) (fun y hy => (speeds y hy).1),
      strictMonoOn_of_deriv_pos (convex_Icc _ _) (con 1) (fun y hy => (speeds y hy).2)⟩
  refine ⟨ε,ep,graphs,?_⟩
  intro z hz w hw eq
  have zform (v : ℂ) : Z v.re v.im=v := by apply Complex.ext <;> simp [Z]
  let s := (H z).re
  have zs : F z.re z.im=s := by dsimp [F,s]; rw [zform]
  have ws : F w.re w.im=s := by
    rw [← zs,zval _ hw.2.1,zval _ hz.2.1,zform,zform,eq]
  obtain ⟨r,_,spec,anti,_⟩ := graphs s hz.2.2
  have xz := (row z.im hz.2.1).injOn hz.1 (Ioo_subset_Icc_self (spec z.im hz.2.1).1) (zs.trans (spec _ hz.2.1).2.symm)
  have xw := (row w.im hw.2.1).injOn hw.1 (Ioo_subset_Icc_self (spec w.im hw.2.1).1) (ws.trans (spec _ hw.2.1).2.symm)
  have yw : z.im=w.im := anti.injOn hz.2.1 hw.2.1 (by
    rw [← xz,← xw,zform,zform,eq])
  exact Complex.ext (xz.trans ((congrArg r yw).trans xw.symm)) yw

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.quarter_rectangle_embedded_height_band
