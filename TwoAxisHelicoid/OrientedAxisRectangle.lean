import TwoAxisHelicoid.AxisSideWindingBound
import TwoAxisHelicoid.AxisRectangleSigns

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology

/-- The sign at one interior point and the absence of interior zeros
determine the sign on the connected rectangle. -/
private theorem rectangle_nonpositive_of_negative {l u : ℝ} {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F (Ioo (0 : ℝ) 1 ×ˢ Ioo l u))
    (hn : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo l u, F p ≠ 0)
    (hex : ∃ p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo l u, F p < 0) :
    ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo l u, F p ≤ 0 := by
  obtain ⟨q,hq,hq'⟩ := hex
  intro p hp
  by_contra! h
  obtain ⟨r,hr,her⟩ := (isPreconnected_Ioo.prod isPreconnected_Ioo).intermediate_value₂ hq hp hF
    (continuousOn_const (c := (0 : ℝ))) hq'.le h.le
  exact hn r hr her

private theorem edge_derivative_nonpos {f : ℝ → ℝ} {d u : ℝ}
    (hu : 0 < u) (h0 : f 0 = 0) (hd : HasDerivAt f d 0)
    (h : ∀ x ∈ Ioo 0 u, f x ≤ 0) : d ≤ 0 := by
  apply le_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [Ioo_mem_nhdsGT hu] with x hx
  simp only [zero_add,h0,sub_zero,smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_pos.mpr hx.1).le (h _ hx)

/-- The inward derivative at one point of the bottom edge fixes
the signs of all inward derivatives on the left edge of both
rectangles when reflection interchanges their signs. -/
theorem oriented_rectangle_edge_signs {t a e : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) {F : ℝ × ℝ → ℝ} {d : ℝ → ℝ}
    (hF : ContinuousOn F (Ioo (0 : ℝ) 1 ×ˢ Ioo 0 t))
    (hn : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo 0 t, F p ≠ 0)
    (hr : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) t, F (x,2*t-y) = -F (x,y))
    (h0 : F (a,0) = 0) (hBd : HasDerivAt (fun y => F (a,y)) e 0) (he : e < 0)
    (hl : ∀ y ∈ Ioo (0 : ℝ) (2*t), F (0,y) = 0)
    (hd : ∀ y ∈ Ioo (0 : ℝ) (2*t), HasDerivAt (fun x => F (x,y)) (d y) 0) :
    (∀ y ∈ Ioo (0 : ℝ) t, d y ≤ 0) ∧ (∀ y ∈ Ioo t (2*t), 0 ≤ d y) := by
  have hex : ∃ p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo 0 t, F p < 0 := by
    by_contra! h
    have he' := edge_derivative_nonpos (f := fun y => -F (a,y)) ht (by rw [h0,neg_zero])
      hBd.neg (fun y hy => neg_nonpos.mpr (h _ ⟨ha,hy⟩))
    linarith
  have hs := rectangle_nonpositive_of_negative hF hn hex
  constructor
  · intro y hy
    have hyy : y ∈ Ioo 0 (2*t) := ⟨hy.1,by linarith [hy.2]⟩
    exact edge_derivative_nonpos (by norm_num : (0 : ℝ) < 1) (hl _ hyy) (hd _ hyy)
      (fun x hx => hs _ ⟨hx,hy⟩)
  · intro y hy
    have hyy : y ∈ Ioo 0 (2*t) := ⟨ht.trans hy.1,hy.2⟩
    have hu : 2*t-y ∈ Ioo 0 t := ⟨by linarith [hy.2],by linarith [hy.1]⟩
    apply neg_nonpos.mp
    apply edge_derivative_nonpos (f := fun x => -F (x,y)) (by norm_num : (0 : ℝ) < 1)
      (by rw [hl _ hyy,neg_zero]) (hd _ hyy).neg
    intro x hx
    have h := hr x hx _ hu
    rw [show 2*t-(2*t-y) = y by ring] at h
    rw [h,neg_neg]
    exact hs _ ⟨hx,hu⟩

private theorem phase_nonpositive_of_sine_nonpositive {l u c : ℝ} (hlu : l < u)
    {f : ℝ → ℝ} (hf : Continuous f) (hc : c ∈ Icc l u) (hfc : f c = 0)
    (hs : ∀ x ∈ Ioo l u, Real.sin (f x) ≤ 0) {x : ℝ} (hx : x ∈ Icc l u) : f x ≤ 0 := by
  have hall : Icc l u ⊆ (fun y => Real.sin (f y)) ⁻¹' Iic 0 := by
    have h := closure_minimal hs (isClosed_Iic.preimage (Real.continuous_sin.comp hf))
    rwa [closure_Ioo hlu.ne] at h
  by_contra! hpos
  let b := min (f x) (Real.pi/2)
  have hb : 0 < b := lt_min hpos (by positivity)
  have hbp : b < Real.pi := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
  obtain ⟨y,hy,hey⟩ := isPreconnected_Icc.intermediate_value₂ hc hx hf.continuousOn
    (continuousOn_const (c := b)) (by rw [hfc]; exact hb.le) (min_le_left _ _)
  have h := hall hy
  change Real.sin (f y) ≤ 0 at h
  rw [hey] at h
  exact (Real.sin_pos_of_pos_of_lt_pi hb hbp).not_ge h

theorem integerAxisPhase_index_positive_of_oriented_sides {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ)
    (hl : ∀ y ∈ Ioo (0 : ℝ) t, Real.sin (integerAxisPhase t a m y) ≤ 0)
    (hr : ∀ y ∈ Ioo t (2*t), 0 ≤ Real.sin (integerAxisPhase t a m y)) :
    1 ≤ m := by
  let f := integerAxisPhase t a m
  have hc : Continuous f := integerAxisPhase_continuous ht ha m
  have hf0 : f t = 0 := integerAxisPhase_midpoint t a m
  have h0 : f 0 ≤ 0 := phase_nonpositive_of_sine_nonpositive ht hc
    (right_mem_Icc.mpr ht.le) hf0 hl (left_mem_Icc.mpr ht.le)
  have htu : t < 2*t := by linarith
  have h2 : -(f (2*t)) ≤ 0 := phase_nonpositive_of_sine_nonpositive htu hc.neg
    (left_mem_Icc.mpr htu.le) (by change -(f t) = 0; rw [hf0,neg_zero])
    (fun y hy => by change Real.sin (-(f y)) ≤ 0; rw [Real.sin_neg]; exact neg_nonpos.mpr (hr y hy)) (right_mem_Icc.mpr htu.le)
  have he := integerAxisPhase_total_increment ht ha m
  change f (2*t)-f 0 = _ at he
  have hm : (0 : ℝ) ≤ 2*(m:ℝ)-1 :=
    (mul_nonneg_iff_of_pos_left (by positivity : 0 < 2*Real.pi)).mp (by rw [← he]; linarith)
  by_contra! h
  have hn : m ≤ 0 := by omega
  have hnR : (m:ℝ) ≤ 0 := by exact_mod_cast hn
  linarith

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.oriented_rectangle_edge_signs
#print axioms TwoAxisHelicoid.integerAxisPhase_index_positive_of_oriented_sides
