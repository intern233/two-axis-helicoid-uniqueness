import TwoAxisHelicoid.ObliqueThetaEdgeSound
import TwoAxisHelicoid.RectangleRealPartBound
import TwoAxisHelicoid.ActualQuarterHeightSlices
import TwoAxisHelicoid.HeightEndAxisCenter

namespace TwoAxisHelicoid
open Complex Set

/-- The three vertical height bounds and two holomorphic rectangles cover
both signs of the physical height down to one quarter, including equality. -/
theorem oblique_theta_tile_from_edges
    (pL : CheckedObliqueEdge true false true (1/2) (23/256) (7/16))
    (pR : CheckedObliqueEdge true false true 1 (23/256) (7/16))
    (pB : CheckedObliqueEdge true false false (23/256) (1/2) 1)
    (pT : CheckedObliqueEdge true false false (7/16) (1/2) 1)
    (pHL : CheckedObliqueEdge true true true (1/2) 0 (7/16))
    (pHR : CheckedObliqueEdge true true true 1 0 (23/256))
    (nL : CheckedObliqueEdge false false true 0 0 (7/16))
    (nR : CheckedObliqueEdge false false true (125/256) 0 (7/16))
    (nB : CheckedObliqueEdge false false false 0 0 (125/256))
    (nT : CheckedObliqueEdge false false false (7/16) 0 (125/256))
    (nH : CheckedObliqueEdge false true true (125/256) 0 (7/16)) :
    let p := certifiedClosedParameters
    let H := actualComplexHeight p.t p.a 1 p.height_pos
    let F := centralPhaseThetaRatio p.t p.a
    ∀ x∈Icc (0:ℝ) 1, ∀ y∈Icc 0 (p.t/2), let z : ℂ := ⟨x,y⟩
      ((1/4:ℝ)≤(H z).re → (obliqueThetaFactor true*F z).re<0) ∧
      ((H z).re≤ -(1/4:ℝ) → (obliqueThetaFactor false*F z).re<0) := by
  intro p H F
  let X := actualGlobalImmersion p.t p.a 1 p.height_pos
  have d : HasTwoAxisHelicoidCoordinateDifferential X p.t p.a 1 p.height_pos := fun z hz =>
    ((actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
      p.vertical_closed p.horizontal_closed).2.2.2 z hz).1
  have top : p.t/2≤7/16 := by have b := certifiedClosedParameters_bounds.1.2; norm_num [rootTUpper] at b; linarith
  have tall : (7/16:ℝ)<p.t := by have b := certifiedClosedParameters_bounds.1.1; norm_num [rootTLower] at b; linarith
  have PL := pL.sound; have PR := pR.sound; have PB := pB.sound; have PT := pT.sound
  have PH := pHL.sound; have PJ := pHR.sound
  have NL := nL.sound; have NR := nR.sound; have NB := nB.sound; have NT := nT.sound; have NH := nH.sound
  norm_num [centralBandEdgePoint] at PL PR PB PT PH PJ NL NR NB NT NH
  have reg {z : ℂ} (hx : z.re∈Icc (0:ℝ) 1) (hy : z.im∈Icc (0:ℝ) (7/16)) : DifferentiableAt ℂ F z := by
    apply (centralPhaseThetaRatio_analyticAt p.height_pos _).differentiableAt
    rcases hy.1.eq_or_lt with e|pos
    · have id : z+p.a=((z.re+p.a:ℝ):ℂ) := by apply Complex.ext <;> simp [e.symm]
      rw [id]
      exact real_not_mem_rhombic_lattice_of_pos p.height_pos (by linarith [hx.1,p.abscissa_mem.1])
        (by linarith [hx.2,p.abscissa_mem.2])
    · exact rhombic_horizontal_strip_not_mem p.height_pos (by
        change (z+(p.a:ℂ)).im∈Ioo 0 p.t
        simpa using And.intro pos (hy.2.trans_lt tall))
  let P := fun (v : Bool) (x y : ℝ) => (obliqueThetaFactor v*F ⟨x,y⟩).re≤ -(1/1024:ℝ)
  have bound {v : Bool} {x y : ℝ} (h : 1/1024+(obliqueThetaFactor v).re*(F ⟨x,y⟩).re≤
      (obliqueThetaFactor v).im*(F ⟨x,y⟩).im) : P v x y := by
    change (obliqueThetaFactor v*F ⟨x,y⟩).re≤ -(1/1024:ℝ)
    rw [Complex.mul_re]
    linarith
  have rectangle (v : Bool) {a b l r : ℝ} (ab : a≤b) (lr : l≤r)
      (xlim : Icc a b⊆Icc 0 1) (ylim : Icc l r⊆Icc 0 (7/16))
      (left : ∀ y∈Icc l r, P v a y) (right : ∀ y∈Icc l r, P v b y)
      (bottom : ∀ x∈Icc a b, P v x l) (top' : ∀ x∈Icc a b, P v x r)
      {x y : ℝ} (hx : x∈Icc a b) (hy : y∈Icc l r) : (obliqueThetaFactor v*F ⟨x,y⟩).re<0 := by
    let f := fun z => -(obliqueThetaFactor v*F z)
    have lo := rectangle_real_lower_bound (f:=f) (m:=1/1024) ab lr
      (fun z hz hw => ((reg (xlim hz) (ylim hw)).const_mul (obliqueThetaFactor v)).neg)
      (fun u hu y hy => by
        rcases (show u=a ∨ u=b by simpa only [mem_insert_iff,mem_singleton_iff] using hu) with rfl|rfl
        · simpa [f,P] using neg_le_neg (left y hy)
        · simpa [f,P] using neg_le_neg (right y hy))
      (fun u hu x hx => by
        rcases (show u=l ∨ u=r by simpa only [mem_insert_iff,mem_singleton_iff] using hu) with rfl|rfl
        · simpa [f,P] using neg_le_neg (bottom x hx)
        · simpa [f,P] using neg_le_neg (top' x hx))
      ⟨x,y⟩ hx hy
    change 1/1024≤ -(obliqueThetaFactor v*F ⟨x,y⟩).re at lo
    linarith
  intro x hx y hy z
  have full : y∈Icc (0:ℝ) (7/16) := ⟨hy.1,hy.2.trans top⟩
  rcases hy.1.eq_or_lt with zero|pos
  · subst y
    have e : (H z).re=0 := actualComplexHeight_ofReal_re p.height_pos x
    exact ⟨fun h => by linarith,fun h => by linarith⟩
  have strip : y∈Ioo 0 p.t := ⟨pos,full.2.trans_lt tall⟩
  have val (u : ℝ) : X ((u:ℂ)+I*y) 2-X 1 2=(H ⟨u,y⟩).re := by
    rw [actual_complex_height_centered_primitive p.height_pos d (rhombic_horizontal_strip_not_mem p.height_pos (by
      change ((u:ℂ)+I*y).im∈Ioo 0 p.t
      simpa using strip))]
    congr 2
    apply Complex.ext <;> simp
  have row : MonotoneOn (fun u : ℝ => (H ⟨u,y⟩).re) (Icc 0 1) := by
    intro u hu v hv le
    change (H ⟨u,y⟩).re≤(H ⟨v,y⟩).re
    rw [← val,← val]
    exact sub_le_sub_right ((actual_quarter_height_row_strictMono p.height_pos strip d).monotoneOn hu hv le) _
  constructor
  · intro high
    by_cases lowX : x≤1/2
    · exact (not_lt_of_ge high ((row hx (by norm_num) lowX).trans_lt (PH y full.1 full.2))).elim
    by_cases lowY : y≤23/256
    · exact (not_lt_of_ge high ((row hx (by norm_num) hx.2).trans_lt (PJ y full.1 lowY))).elim
    exact rectangle true (a:=1/2) (b:=1) (l:=23/256) (r:=7/16) (by norm_num) (by norm_num)
      (Icc_subset_Icc (by norm_num) le_rfl) (Icc_subset_Icc (by norm_num) le_rfl)
      (fun _ h => bound (PL _ h.1 h.2)) (fun _ h => bound (PR _ h.1 h.2))
      (fun _ h => bound (PB _ h.1 h.2)) (fun _ h => bound (PT _ h.1 h.2))
      ⟨(not_le.mp lowX).le,hx.2⟩ ⟨(not_le.mp lowY).le,full.2⟩
  · intro low
    by_cases highX : 125/256≤x
    · have cmp := row (show (125/256:ℝ)∈Icc 0 1 by norm_num) hx highX
      have gate := NH y full.1 full.2
      change (H ⟨x,y⟩).re≤ -(1/4:ℝ) at low
      change -(H ⟨125/256,y⟩).re<1/4 at gate
      linarith
    exact rectangle false (a:=0) (b:=125/256) (l:=0) (r:=7/16) (by norm_num) (by norm_num)
      (Icc_subset_Icc le_rfl (by norm_num)) Subset.rfl
      (fun _ h => bound (NL _ h.1 h.2)) (fun _ h => bound (NR _ h.1 h.2))
      (fun _ h => bound (NB _ h.1 h.2)) (fun _ h => bound (NT _ h.1 h.2))
      ⟨hx.1,(not_le.mp highX).le⟩ full

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.oblique_theta_tile_from_edges
