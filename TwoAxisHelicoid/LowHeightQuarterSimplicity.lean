import TwoAxisHelicoid.LowLevelQuarterMonotonicity
import TwoAxisHelicoid.PositiveLevelQuarterReduction
import TwoAxisHelicoid.CertifiedQuarterHeightRows

namespace TwoAxisHelicoid
open Complex Set

/-- Four position bounds and two overlapping velocity signs exclude
all pairs of distinct parameters in the actual low positive quarter.
The horizontal coordinate at the lower cutoff and at the midpoint is
bounded by the genuine height equation. -/
theorem low_height_quarter_simple_from_windows :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    let H := actualComplexHeight p.t p.a 1 p.height_pos
    let G := thetaGauss p.t p.a 1
    let P := fun z : ℂ => X z 0-X 1 0
    let Y := fun z : ℂ => X z 1-X 1 1
    (1/4<(H ⟨1,7/32⟩).re) →
    (∀ x∈Icc (0:ℝ) 1, 0<(H ⟨x,7/32⟩).re → 9/16<x) →
    (∀ x∈Icc (0:ℝ) 1, ∀ y∈Icc (3/8:ℝ) (1/2), (H ⟨x,y⟩).re∈Ioc (0:ℝ) (1/4) → x∈Icc (15/32:ℝ) (3/5)) →
    (∀ x∈Icc (0:ℝ) 1, ∀ y∈Ioc (0:ℝ) (7/32), 0<(H ⟨x,y⟩).re → 1/2≤x) →
    (∀ z : ℂ, z.re∈Icc (0:ℝ) 1 → z.im∈Ioc (0:ℝ) (3/8) → 0<(H z).re → (G z).re<0) →
    (∀ z : ℂ, z.re∈Icc (0:ℝ) 1 → z.im∈Ioo (0:ℝ) p.t → 7/32≤z.im → (H z).re∈Ioc (0:ℝ) (1/4) → (G z).im<0) →
    (∀ x∈Icc (1/2:ℝ) 1, ∀ y∈Icc (0:ℝ) (7/32), 0≤P ⟨x,y⟩) →
    (∀ x∈Icc (9/16:ℝ) 1, Y ⟨x,7/32⟩≤5/4) →
    (∀ x∈Icc (15/32:ℝ) (3/5), ∀ y∈Icc (3/8:ℝ) (1/2), 5/4<Y ⟨x,y⟩) →
    (∀ x∈Icc (15/32:ℝ) (3/5), P ⟨x,1/2⟩<0) →
    ∀ h∈Ioc (0:ℝ) (1/4), InjOn X {z : ℂ | z.re∈Ioc (0:ℝ) 1 ∧ z.im∈Ioo (0:ℝ) p.t ∧ X z 2=X 1 2+h} := by
  intro p X H G P Y axisPoint earlyX middleX leftX gReal gImag earlyP earlyY middleY lateP h hh
  have geom := actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
    p.vertical_closed p.horizontal_closed
  have d : HasTwoAxisHelicoidCoordinateDifferential X p.t p.a 1 p.height_pos := fun z hz => (geom.2.2.2 z hz).1
  obtain ⟨b,hb,r,base,cont,_,inside,graph⟩ := positive_quarter_height_ray p.height_pos p.abscissa_mem hh.1 d geom.1
  let J := Ico b p.t
  let Z := fun y : ℝ => (r y:ℂ)+I*y
  let F := fun y : ℝ => X (Z y)-X 1
  have tl := (by norm_num [rootTLower] : (1/2:ℝ)<rootTLower).trans certifiedClosedParameters_bounds.1.1
  have eq (x y : ℝ) : (x:ℂ)+I*y=⟨x,y⟩ := by apply Complex.ext <;> simp
  have yt {y : ℝ} (hy : y∈J) : y∈Ioo 0 p.t := ⟨hb.1.trans_le hy.1,hy.2⟩
  have off {x y : ℝ} (hy : y∈Ioo 0 p.t) : ((x:ℂ)+I*y)∉certifiedPeriodPair.lattice :=
    rhombic_horizontal_strip_not_mem p.height_pos (by change ((x:ℂ)+I*y).im∈Ioo 0 p.t; simpa using hy)
  have xr {y : ℝ} (hy : y∈J) : r y∈Icc (0:ℝ) 1 := by
    rcases hy.1.eq_or_lt with lo|lo
    · rw [← lo,base]; norm_num
    · exact Ioo_subset_Icc_self (inside y ⟨lo,hy.2⟩)
  have on (y : ℝ) (hy : y∈J) : X (Z y) 2=X 1 2+h := (graph y (yt hy) (r y) (xr hy)).mpr ⟨hy.1,rfl⟩
  have inH {y : ℝ} (hy : y∈J) : (H (Z y)).re=h := by
    rw [← actual_complex_height_centered_primitive p.height_pos d (off (yt hy)),on y hy]
    ring
  have inBox {y : ℝ} (hy : y∈J) : (H ⟨r y,y⟩).re∈Ioc (0:ℝ) (1/4) := by
    rw [← eq,inH hy]
    exact hh
  have ll : (7/32:ℝ)∈Ioo 0 p.t := ⟨by norm_num,by linarith⟩
  have before : b<7/32 := by
    have g := actual_complex_height_centered_primitive p.height_pos d (off (x:=1) ll)
    rw [eq] at g
    have past : X (1+I*(7/32:ℝ)) 2>X 1 2+h := by
      rw [← eq,ofReal_one] at g axisPoint
      linarith [hh.2]
    have start := on b (show b∈J from ⟨le_rfl,hb.2⟩)
    change X ((r b:ℂ)+I*b) 2=X 1 2+h at start
    rw [base,ofReal_one] at start
    exact ((actual_vertical_axis_height_strictMono p.height_pos p.abscissa_mem d).lt_iff_lt
      (show b∈Ioo (-p.t) p.t from ⟨by linarith [hb.1,p.height_pos],hb.2⟩)
      (show (7/32:ℝ)∈Ioo (-p.t) p.t from ⟨by linarith [p.height_pos],ll.2⟩)).mp (start.trans_lt past)
  have uT : (3/8:ℝ)<p.t := by linarith
  have wl : (7/32:ℝ)≤3/8 := by norm_num
  have lateIn : (1/2:ℝ)∈J := ⟨by linarith,tl⟩
  have earlyIn : (7/32:ℝ)∈J := ⟨before.le,ll.2⟩
  have bounds := low_level_quarter_monotone_windows p.height_pos p.abscissa_mem before uT hb.1 d cont inside on (by
    intro y hy
    have mem : y∈J := ⟨hy.1.le,hy.2.trans uT⟩
    change (G ((r y:ℂ)+I*y)).re<0
    rw [eq]
    exact gReal _ (xr mem) ⟨(yt mem).1,hy.2.le⟩ (inBox mem).1) (by
    intro y hy
    have mem : y∈J := ⟨before.le.trans hy.1.le,hy.2⟩
    change (G ((r y:ℂ)+I*y)).im<0
    rw [eq]
    exact gImag _ (xr mem) (yt mem) hy.1.le (inBox mem))
  have inj : InjOn F J := quarter_arc_injective_from_windows (C:=5/4) (w:=1/2) bounds.1 bounds.2 (by
    intro y hy below
    have left := leftX _ (xr hy) _ ⟨(yt hy).1,below.le⟩ (inBox hy).1
    have first := earlyP _ ⟨left,(xr hy).2⟩ _ ⟨(yt hy).1.le,below.le⟩
    have cap := earlyY _ ⟨(earlyX _ (xr earlyIn) (inBox earlyIn).1).le,(xr earlyIn).2⟩
    have mono := bounds.1.monotoneOn (show y∈Icc b (3/8) from ⟨hy.1,below.le.trans wl⟩) ⟨before.le,wl⟩ below.le
    change F y 1≤F (7/32) 1 at mono
    refine ⟨?_,mono.trans ?_⟩
    · simpa only [F,Z,P,Y,Pi.sub_apply,eq] using first
    · simpa only [F,Z,P,Y,Pi.sub_apply,eq] using cap) (by
    intro y hy order mid
    have row : y∈Icc (3/8:ℝ) (1/2) := ⟨order.le,mid⟩
    have edge := middleY _ (middleX _ (xr hy) _ row (inBox hy)) _ row
    simpa only [F,Z,P,Y,Pi.sub_apply,eq] using edge) (by
    intro y hy beyond
    have pos := lateP _ (middleX _ (xr lateIn) _ (by norm_num) (inBox lateIn))
    have anti := bounds.2.antitoneOn (show (1/2:ℝ)∈Ico (7/32:ℝ) p.t from ⟨by norm_num,tl⟩)
      (show y∈Ico (7/32:ℝ) p.t from ⟨by linarith,hy.2⟩) beyond.le
    change F y 0≤F (1/2) 0 at anti
    apply anti.trans_lt
    simpa only [F,Z,P,Y,Pi.sub_apply,eq] using pos)
  have point {z : ℂ} (hz : z.re∈Ioc (0:ℝ) 1 ∧ z.im∈Ioo (0:ℝ) p.t ∧ X z 2=X 1 2+h) : z.im∈J ∧ Z z.im=z := by
    have val := (graph z.im hz.2.1 z.re ⟨hz.1.1.le,hz.1.2⟩).mp (by change X ((z.re:ℂ)+I*z.im) 2=_; rw [eq]; exact hz.2.2)
    refine ⟨⟨val.1,hz.2.1.2⟩,?_⟩
    rw [show Z z.im=⟨r z.im,z.im⟩ from eq _ _,← val.2]
  intro z hz w hw same
  obtain ⟨mz,ez⟩ := point hz
  obtain ⟨mw,ew⟩ := point hw
  have y := inj mz mw (by change X (Z z.im)-X 1=X (Z w.im)-X 1; rw [ez,ew,same])
  exact ez.symm.trans ((congrArg Z y).trans ew)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.low_height_quarter_simple_from_windows
