import TwoAxisHelicoid.RectangleRowLevelGraph
import TwoAxisHelicoid.QuarterRowSpatialVelocity
import Mathlib.Analysis.Convex.Function

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology

/-- Convex and increasing vertical edges keep a whole segment in each
physical height fiber. A Gauss component of one sign then proves
injectivity of projection onto a vertical plane on the closed rectangle. -/
theorem quarter_rectangle_vertical_projection {t a L R B T : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    (lx : 0<L) (lr : L≤R) (rx : R<1) (by0 : 0<B) (ty : T<t)
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht) :
    let Z := fun x y : ℝ => (x:ℂ)+I*y
    let H := actualComplexHeight t a 1 ht
    let J := Icc B T
    let C := Icc L R
    ConvexOn ℝ J (fun y => (H (Z L y)).re) →
    MonotoneOn (fun y => (H (Z R y)).re) J →
    (∀ z : ℂ, z.re∈C → z.im∈J → (thetaGauss t a 1 z).im<0) →
    InjOn (fun z => ((H z).re,X z 0)) {z | z.re∈C ∧ z.im∈J} := by
  intro Z H J C cv mono sign
  let F := fun p : ℝ × ℝ => (H (Z p.1 p.2)).re
  have xR {x : ℝ} (hx : x∈C) : x∈Ioo (0:ℝ) 1 := ⟨lx.trans_le hx.1,hx.2.trans_lt rx⟩
  have yR {y : ℝ} (hy : y∈J) : y∈Ioo 0 t := ⟨by0.trans_le hy.1,hy.2.trans_lt ty⟩
  have off (x y : ℝ) (hy : y∈J) : Z x y∉(rhombicPeriodPair t ht).lattice := rhombic_horizontal_strip_not_mem ht (by
    change (Z x y).im∈Ioo 0 t
    simpa [Z] using yR hy)
  have zform (v : ℂ) : Z v.re v.im=v := by apply Complex.ext <;> simp [Z]
  have rows (y : ℝ) (hy : y∈J) : StrictMonoOn (fun x => F (x,y)) C := by
    intro x hx u hu lt
    change (H (Z x y)).re<(H (Z u y)).re
    rw [← actual_complex_height_centered_primitive ht d (off x y hy),← actual_complex_height_centered_primitive ht d (off u y hy)]
    exact sub_lt_sub_right (actual_quarter_height_row_strictMono ht (yR hy) d
      (Ioo_subset_Icc_self (xR hx)) (Ioo_subset_Icc_self (xR hu)) lt) _
  have order (z w : ℂ) (hz : z.re∈C ∧ z.im∈J) (hw : w.re∈C ∧ w.im∈J) (ord : z.im≤w.im)
      (height : (H z).re=(H w).re) (horizontal : X z 0=X w 0) : z=w := by
    let s := (H z).re
    let D := Icc z.im w.im
    have sub : D⊆J := Icc_subset_Icc hz.2.1 hw.2.2
    have ez : F (z.re,z.im)=s := by dsimp only [F,s]; rw [zform]
    have ew : F (w.re,w.im)=s := by dsimp only [F,s]; rw [zform,height]
    have lmem : L∈C := left_mem_Icc.mpr lr
    have rmem : R∈C := right_mem_Icc.mpr lr
    have leftz := ((rows _ hz.2).monotoneOn lmem hz.1 hz.1.1).trans_eq ez
    have leftw := ((rows _ hw.2).monotoneOn lmem hw.1 hw.1.1).trans_eq ew
    have rightz := ez.symm.trans_le ((rows _ hz.2).monotoneOn hz.1 rmem hz.1.2)
    have edge (y : ℝ) (hy : y∈D) : F (L,y)≤s ∧ s≤F (R,y) :=
      ⟨((cv.convex_le s).ordConnected.out ⟨hz.2,leftz⟩ ⟨hw.2,leftw⟩ hy).2,
       rightz.trans (mono hz.2 (sub hy) hy.1)⟩
    have fc : ContinuousOn F (C ×ˢ D) := by
      intro p hp
      have line : Continuous (fun q : ℝ × ℝ => Z q.1 q.2) := by dsimp [Z]; fun_prop
      exact (continuous_re.continuousAt.comp ((actualComplexHeight_hasDerivAt (a:=a) (c:=1) ht (off p.1 p.2 (sub hp.2))).continuousAt.comp (f:=fun q : ℝ × ℝ => Z q.1 q.2) (line.continuousAt (x:=p)))).continuousWithinAt
    obtain ⟨r,cr,spec⟩ := rectangle_closed_row_graph lr fc (fun _ hy => rows _ (sub hy)) edge
    let W := fun y => Z (r y) y
    have cw (y : ℝ) (hy : y∈D) : ContinuousWithinAt W D y :=
      (continuous_ofReal.continuousAt.comp_continuousWithinAt (cr y hy)).add (continuous_const.mul continuous_ofReal).continuousAt.continuousWithinAt
    have anti : StrictAntiOn (fun y => X (W y) 0) D := by
      apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (fun y hy =>
        ((continuous_apply 0).continuousAt.comp_continuousWithinAt ((d (W y) (off (r y) y (sub hy))).continuousAt.comp_continuousWithinAt (f:=W) (cw y hy))))
      intro y hy
      have h := interior_subset hy
      have near := mem_interior_iff_mem_nhds.mp hy
      obtain ⟨k,kp,velocity⟩ := quarter_row_spatial_velocity ht ha d ((cr y h).continuousAt near) (yR (sub h)) (xR (spec y h).1)
        (s:=s) (by filter_upwards [near] with v hv using (spec v hv).2)
      have wx : (W y).re=r y := by simp [W,Z]
      have wy : (W y).im=y := by simp [W,Z]
      exact (hasDerivAt_pi.mp velocity 0).deriv.trans_lt (mul_neg_of_pos_of_neg kp
        (sign (W y) (wx.symm ▸ (spec y h).1) (wy.symm ▸ sub h)))
    have zu : z.im∈D := left_mem_Icc.mpr ord
    have wv : w.im∈D := right_mem_Icc.mpr ord
    have xz := (rows _ hz.2).injOn hz.1 (spec _ zu).1 (ez.trans (spec _ zu).2.symm)
    have xw := (rows _ hw.2).injOn hw.1 (spec _ wv).1 (ew.trans (spec _ wv).2.symm)
    have yw : z.im=w.im := anti.injOn zu wv (by
      dsimp only [W]
      rw [← xz,← xw,zform,zform,horizontal])
    exact Complex.ext (xz.trans ((congrArg r yw).trans xw.symm)) yw
  intro z hz w hw e
  rcases le_total z.im w.im with h|h
  · exact order z w hz hw h (congrArg Prod.fst e) (congrArg Prod.snd e)
  · exact (order w z hw hz h (congrArg Prod.fst e.symm) (congrArg Prod.snd e.symm)).symm

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.quarter_rectangle_vertical_projection
