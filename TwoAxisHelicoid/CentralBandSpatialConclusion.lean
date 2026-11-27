import TwoAxisHelicoid.CentralBandEdgeSound
import TwoAxisHelicoid.GaussRectangleMaximum
import TwoAxisHelicoid.CentralBandLevelGraphs

namespace TwoAxisHelicoid
open Complex Set

/-- Six edge enclosures imply a Gauss quadrant on the entire rectangle
and injectivity on the open height band it cuts from the surface. -/
theorem central_band_spatial_conclusion
    (leftH : CheckedCentralBandEdge .heightNeg true (1/2) (1/8) (3/8))
    (rightH : CheckedCentralBandEdge .heightPos true (5/8) (1/8) (3/8))
    (leftG : CheckedCentralBandEdge .gauss true (1/2) (1/8) (3/8))
    (rightG : CheckedCentralBandEdge .gauss true (5/8) (1/8) (3/8))
    (bottom : CheckedCentralBandEdge .gauss false (1/8) (1/2) (5/8))
    (top : CheckedCentralBandEdge .gauss false (3/8) (1/2) (5/8)) :
    let p := certifiedClosedParameters
    let H := actualComplexHeight p.t p.a 1 p.height_pos
    let G := thetaGauss p.t p.a 1
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    let J := Icc (1/8:ℝ) (3/8)
    let K := Icc (1/2:ℝ) (5/8)
    (∀ z : ℂ, z.re∈K → z.im∈J → (G z).re≤ -(1/512) ∧ (G z).im≤ -(1/512)) ∧
    ∃ ε : ℝ, 0<ε ∧
      (∀ s : ℝ, |s|<ε → ∃ r : ℝ → ℝ, ContinuousOn r J ∧
        (∀ y∈J, r y∈Ioo (1/2:ℝ) (5/8) ∧ (H ((r y:ℂ)+I*y)).re=s) ∧
          StrictAntiOn (fun y => X ((r y:ℂ)+I*y) 0) J ∧ StrictMonoOn (fun y => X ((r y:ℂ)+I*y) 1) J) ∧
      InjOn X {z | z.re∈K ∧ z.im∈J ∧ |(H z).re|<ε} := by
  intro p H G X J K
  have lt : (3/8:ℝ)<p.t := by
    have e := certifiedClosedParameters_bounds.1.1
    exact (by norm_num [rootTLower] : (3/8:ℝ)<rootTLower).trans e
  have yR {y : ℝ} (hy : y∈J) : y∈Ioo 0 p.t := ⟨by linarith [hy.1],hy.2.trans_lt lt⟩
  have JJ {y : ℝ} (hy : y∈J) : y∈Icc ((1/8:ℚ):ℝ) ((3/8:ℚ):ℝ) := by norm_num at hy ⊢; exact hy
  have KK {x : ℝ} (hx : x∈K) : x∈Icc ((1/2:ℚ):ℝ) ((5/8:ℚ):ℝ) := by norm_num at hx ⊢; exact hx
  have analytic (z : ℂ) (_ : z.re∈K) (hy : z.im∈J) : DifferentiableAt ℂ G z := by
    have m : z-p.a∉certifiedPeriodPair.lattice := rhombic_horizontal_strip_not_mem p.height_pos
      (by change (z-p.a).im∈Ioo 0 p.t; simpa only [sub_im,ofReal_im,sub_zero] using yR hy)
    have n : z+p.a∉certifiedPeriodPair.lattice := rhombic_horizontal_strip_not_mem p.height_pos
      (by change (z+p.a).im∈Ioo 0 p.t; simpa only [add_im,ofReal_im,add_zero] using yR hy)
    exact (thetaGauss_hasDerivAt p.height_pos p.a 1 (rhombic_horizontal_strip_not_mem p.height_pos (yR hy)) m n).differentiableAt
  have quadrant := complex_rectangle_component_bounds (a:=(1/2:ℝ)) (b:=5/8) (c:=1/8) (d:=3/8)
    (M:= -(1/512)) (by norm_num) (by norm_num) (g:=G) analytic (by
      intro x hx y hy
      rcases hx with rfl|hx
      · simpa [CentralBandQuantity.holds,centralBandEdgePoint] using leftG.sound y (JJ hy) (yR hy)
      · obtain rfl := mem_singleton_iff.mp hx
        simpa [CentralBandQuantity.holds,centralBandEdgePoint] using rightG.sound y (JJ hy) (yR hy)) (by
      intro y hy x hx
      have bl : (1/8:ℝ)∈J := left_mem_Icc.mpr (by norm_num)
      have tr : (3/8:ℝ)∈J := right_mem_Icc.mpr (by norm_num)
      rcases hy with rfl|hy
      · have val := bottom.sound x (KK hx) (by change ((1/8:ℚ):ℝ)∈Ioo 0 p.t; simpa using yR bl)
        simpa [CentralBandQuantity.holds,centralBandEdgePoint] using val
      · obtain rfl := mem_singleton_iff.mp hy
        have val := top.sound x (KK hx) (by change ((3/8:ℚ):ℝ)∈Ioo 0 p.t; simpa using yR tr)
        simpa [CentralBandQuantity.holds,centralBandEdgePoint] using val)
  have d : HasTwoAxisHelicoidCoordinateDifferential X p.t p.a 1 p.height_pos := fun z hz =>
    ((actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
      p.vertical_closed p.horizontal_closed).2.2.2 z hz).1
  refine ⟨quadrant,quarter_rectangle_embedded_height_band (L:=1/2) (R:=5/8) (B:=1/8) (T:=3/8) p.height_pos p.abscissa_mem
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) lt d ?_ ?_⟩
  · intro y hy
    have a := leftH.sound y (JJ hy) (yR hy)
    have b := rightH.sound y (JJ hy) (yR hy)
    have repr (x : ℝ) : (x:ℂ)+I*y=⟨x,y⟩ := by apply Complex.ext <;> simp
    change (H (((1/2:ℝ):ℂ)+I*y)).re<0 ∧ 0<(H (((5/8:ℝ):ℂ)+I*y)).re
    rw [repr,repr]
    exact ⟨by simpa [CentralBandQuantity.holds,centralBandEdgePoint] using a,by simpa [CentralBandQuantity.holds,centralBandEdgePoint] using b⟩
  · intro x hx y hy
    have e := quadrant ((x:ℂ)+I*y) (by simpa using hx) (by simpa using hy)
    exact ⟨e.1.trans_lt (by norm_num),e.2.trans_lt (by norm_num)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.central_band_spatial_conclusion
