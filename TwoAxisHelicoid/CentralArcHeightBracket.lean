import TwoAxisHelicoid.CentralArcHeightSound
import TwoAxisHelicoid.RectangleThetaQuadrant
import TwoAxisHelicoid.QuarterRelativeGaussCoordinate
import TwoAxisHelicoid.GaussRealCoefficients

namespace TwoAxisHelicoid
open Complex Set
attribute [local irreducible] thetaJet thetaLogSecond thetaLogThird thetaLogFourth

private theorem central_sweep_saddle_increase {F V W : ℝ → ℝ} {m b : ℝ} (bp : 0<b)
    (slope : ∀ y∈Icc 0 m, HasDerivAt F (V y) y)
    (first : ∀ y∈Icc 0 b, HasDerivAt V (W y) y)
    (second : ∀ y∈Icc 0 b, ∃ v : ℝ, 0<v ∧ HasDerivAt W v y)
    (w0 : W 0=0) (v0 : V 0=0) (positive : ∀ y∈Icc b m, 0<V y) : StrictMonoOn F (Icc 0 m) := by
  have zero : (0:ℝ)∈Icc 0 b := left_mem_Icc.mpr bp.le
  have incW : StrictMonoOn W (Icc 0 b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (fun y hy => (second y hy).choose_spec.2.continuousAt.continuousWithinAt)
    intro y hy
    obtain ⟨v,vp,der⟩ := second y (interior_subset hy)
    rwa [der.deriv]
  have incV : StrictMonoOn V (Icc 0 b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (fun y hy => (first y hy).continuousAt.continuousWithinAt)
    intro y hy
    rw [interior_Icc] at hy
    have i := incW zero ⟨hy.1.le,hy.2.le⟩ hy.1
    rwa [(first y ⟨hy.1.le,hy.2.le⟩).deriv,← w0]
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (fun y hy => (slope y hy).continuousAt.continuousWithinAt)
  intro y hy
  rw [interior_Icc] at hy
  rw [(slope y ⟨hy.1.le,hy.2.le⟩).deriv]
  rcases le_total y b with e|e
  · exact v0 ▸ incV zero ⟨hy.1.le,e⟩ hy.1
  · exact positive y ⟨e,hy.2.le⟩

/-- The four one-dimensional enclosures, together with the previously checked
middle left edge, give a bracket bounded by the saddle itself on every row. -/
theorem central_arc_height_boundary_signs {t a : ℝ} (tb : t∈Icc (rootTLower:ℝ) rootTUpper)
    (ab : a∈Icc (rootALower:ℝ) rootAUpper) (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) (root : thetaG t a=0)
    (early : CheckedCentralHeightSweep .leftEarly 0 (1/8)) (late : CheckedCentralHeightSweep .leftLate (3/8) (7/16))
    (third : CheckedCentralHeightSweep .saddleThird 0 (1/8)) (upper : CheckedCentralHeightSweep .saddleSlope (1/8) (7/16)) :
    let H := actualComplexHeight t a 1 ht
    let F := fun x y : ℝ => (H ((x:ℂ)+I*y)).re
    F (1/2) (t/2)=0 → (∀ y∈Icc (1/8:ℝ) (3/8), F (1/2) y<0) →
      StrictMonoOn (F a) (Icc 0 (t/2)) ∧ ∀ y∈Ioo 0 (t/2), F (1/2) y<0 ∧ 0<F a y := by
  intro H F midpoint middle
  let Z := fun x y : ℝ => (x:ℂ)+I*y
  let V := fun x y : ℝ => Real.pi/t-(thetaLogSecond t (Z x y)).re
  let W := fun x y : ℝ => (thetaLogThird t (Z x y)).im
  let L := rhombicPeriodPair t ht
  have tm₁ : (3/8:ℝ)<t/2 := by have q := tb.1; norm_num [rootTLower] at q; linarith
  have tm₂ : t/2≤(7/16:ℝ) := by have q := tb.2; norm_num [rootTUpper] at q; linarith
  have smaller : (7/16:ℝ)<t := by have q := tb.1; norm_num [rootTLower] at q; linarith
  have regular {x y : ℝ} (hx : x∈Ioo (0:ℝ) 1) (hy : y∈Icc (0:ℝ) (7/16)) : Z x y∉L.lattice := by
    rcases hy.1.eq_or_lt with h|h
    · rw [← h,show Z x 0=(x:ℂ) by simp [Z]]
      exact real_not_mem_rhombic_lattice_of_pos ht hx.1 (by linarith [hx.2])
    · exact rhombic_horizontal_strip_not_mem ht (by
        change (Z x y).im∈Ioo 0 t
        simpa [Z] using And.intro h (hy.2.trans_lt smaller))
  have va := thetaG_eq_weierstrassP_of_pos ht ht a (real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2]))
  rw [root] at va
  have first (x y : ℝ) (hx : x∈Ioo (0:ℝ) 1) (hy : y∈Icc (0:ℝ) (7/16)) : HasDerivAt (F x) (V x y) y := by
    have hd := (vertical_line_real_derivatives (actualComplexHeight_hasDerivAt (a:=a) (c:=1) ht (regular hx hy))).1
    have he := thetaLogSecond_eq_weierstrassP_add_eta_of_pos ht ht (regular hx hy)
    have alg : (L.weierstrassP (Z x y)-L.weierstrassP a)=thetaLogSecond t (Z x y)-((Real.pi/t:ℝ):ℂ) := by
      dsimp [L]
      linear_combination va-he
    change HasDerivAt (F x) (-(I*(1:ℂ)*(L.weierstrassP (Z x y)-L.weierstrassP a)).im) y at hd
    simpa only [V,alg,mul_one,I_mul_im,sub_re,ofReal_re,neg_sub] using hd
  have base (x : ℝ) : F x 0=0 := by simp [F,H,actualComplexHeight,Complex.mul_re,Complex.mul_im,thetaZeta_real,rhombic_weierstrassP_real]
  have oneHalf : (1/2:ℝ)∈Ioo 0 1 := by constructor <;> norm_num
  have win {y : ℝ} (h : y∈Icc (0:ℝ) (1/8)) : y∈Icc (0:ℝ) (7/16) := ⟨h.1,h.2.trans (by norm_num)⟩
  have exactDer (y : ℝ) (hy : y∈Icc (0:ℝ) (1/8)) :
      HasDerivAt (V a) (W a y) y ∧ HasDerivAt (W a) (thetaLogFourth t (Z a y)).re y := by
    have nz := mt (thetaJet_zero_iff_rhombic_lattice_of_pos ht (Z a y)).mp (regular ha (win hy))
    have d := (vertical_line_real_derivatives (thetaLogSecond_hasDerivAt_of_pos ht nz)).1.const_sub (Real.pi/t)
    exact ⟨by simpa only [neg_neg] using d,(vertical_line_real_derivatives (thetaLogThird_hasDerivAt ht nz)).2⟩
  have z0 : Z a 0=(a:ℂ) := by simp [Z]
  have v0 : V a 0=0 := by
    have h := thetaLogSecond_eq_weierstrassP_add_eta_of_pos ht ht (regular ha (win (left_mem_Icc.mpr (by norm_num))))
    rw [z0] at h
    have eq : thetaLogSecond t (a:ℂ)=((Real.pi/t:ℝ):ℂ) := by linear_combination h-va
    simp [V,z0,eq]
  have w0 : W a 0=0 := by
    have reg := real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2])
    dsimp only [W]
    rw [z0,thetaLogThird_eq_weierstrassP_deriv ht reg,real_wp_derivative_as_real ht ha,ofReal_im]
  have inc := central_sweep_saddle_increase (m:=t/2) (b:=1/8) (by norm_num)
    (fun y hy => first a y ha ⟨hy.1,hy.2.trans tm₂⟩) (fun y hy => (exactDer y hy).1)
    (fun y hy => ⟨_,third.sound tb ab y (by norm_num at hy ⊢; exact hy),(exactDer y hy).2⟩) w0 v0
    (fun y hy => upper.sound tb ab y (by norm_num; exact ⟨hy.1,hy.2.trans tm₂⟩))
  refine ⟨inc,fun y hy => ⟨?_,(base a) ▸ inc (left_mem_Icc.mpr (half_pos ht).le) ⟨hy.1.le,hy.2.le⟩ hy.1⟩⟩
  by_cases small : y≤1/8
  · have dec : StrictAntiOn (F (1/2)) (Icc (0:ℝ) (1/8)) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (fun v hv => (first _ _ oneHalf (win hv)).continuousAt.continuousWithinAt)
      intro u hu
      have v := interior_subset hu
      have p := early.sound tb ab u (by norm_num; exact v)
      change 0< -(V (1/2) u) at p
      rw [(first _ _ oneHalf (win v)).deriv]
      linarith
    exact (dec (left_mem_Icc.mpr (by norm_num)) ⟨hy.1.le,small⟩ hy.1).trans_eq (base _)
  by_cases mid : y≤3/8
  · exact middle y ⟨le_of_not_ge small,mid⟩
  have close (v : ℝ) (hv : v∈Icc (3/8:ℝ) (t/2)) : v∈Icc (0:ℝ) (7/16) :=
    ⟨(by norm_num : (0:ℝ)≤3/8).trans hv.1,hv.2.trans tm₂⟩
  have last : StrictMonoOn (F (1/2)) (Icc (3/8:ℝ) (t/2)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (fun v hv => (first _ _ oneHalf (close v hv)).continuousAt.continuousWithinAt)
    intro u hu
    have v := interior_subset hu
    rw [(first _ _ oneHalf (close u v)).deriv]
    exact late.sound tb ab u (by norm_num; exact ⟨v.1,v.2.trans tm₂⟩)
  exact (last ⟨le_of_not_ge mid,hy.2.le⟩ (right_mem_Icc.mpr tm₁.le) hy.2).trans_eq midpoint

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.central_arc_height_boundary_signs
