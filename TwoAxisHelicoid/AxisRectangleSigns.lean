import TwoAxisHelicoid.AxisHelicoidCalibration
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped ComplexConjugate Topology

/-- A continuous function without zeros on an open rectangle has a single
sign there. If it vanishes along the left edge, all its inward
derivatives on that edge have a single weak sign. -/
theorem rectangle_boundary_derivatives_one_sign {l u : ℝ} {F : ℝ × ℝ → ℝ} {d : ℝ → ℝ}
    (hF : ContinuousOn F (Ioo (0 : ℝ) 1 ×ˢ Ioo l u))
    (hn : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo l u, F p ≠ 0)
    (h0 : ∀ y ∈ Ioo l u, F (0,y) = 0)
    (hd : ∀ y ∈ Ioo l u, HasDerivAt (fun x => F (x,y)) (d y) 0) :
    (∀ y ∈ Ioo l u, 0 ≤ d y) ∨ (∀ y ∈ Ioo l u, d y ≤ 0) := by
  let R := Ioo (0 : ℝ) 1 ×ˢ Ioo l u
  have hsign : (∀ p ∈ R, 0 ≤ F p) ∨ (∀ p ∈ R, F p ≤ 0) := by
    by_cases h : ∀ p ∈ R, 0 ≤ F p
    · exact Or.inl h
    push Not at h
    obtain ⟨p,hp,hfp⟩ := h
    refine Or.inr fun q hq => ?_
    by_contra! hq'
    obtain ⟨s,hs,hes⟩ := (isPreconnected_Ioo.prod isPreconnected_Ioo).intermediate_value₂ hp hq hF
      (continuousOn_const (c := (0 : ℝ))) hfp.le hq'.le
    exact hn s hs hes
  have he : ∀ᶠ x : ℝ in 𝓝[>] 0, x ∈ Ioo (0 : ℝ) 1 :=
    Ioo_mem_nhdsGT (by norm_num)
  rcases hsign with h | h
  · left
    intro y hy
    apply ge_of_tendsto ((hd y hy).tendsto_slope_zero_right)
    filter_upwards [he] with x hx
    simp only [zero_add,h0 y hy,sub_zero,smul_eq_mul]
    exact mul_nonneg (inv_pos.mpr hx.1).le (h _ ⟨hx,hy⟩)
  · right
    intro y hy
    apply le_of_tendsto ((hd y hy).tendsto_slope_zero_right)
    filter_upwards [he] with x hx
    simp only [zero_add,h0 y hy,sub_zero,smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_pos.mpr hx.1).le (h _ ⟨hx,hy⟩)

/-- In the interior between successive horizontal reflection lines and
successive vertical reflection lines, injectivity on the punctured
quotient prevents the image from meeting either straight axis. -/
theorem harmonic_embedded_rectangle_avoids_axes {t x y : ℝ} (ht : 0 < t)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) (2*t)) (hn : y ≠ t)
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hXi : ∀ z ∉ (rhombicPeriodPair t ht).lattice, ∀ w ∉ (rhombicPeriodPair t ht).lattice,
      X z = X w → periodTorusProjection (rhombicPeriodPair t ht) z =
        periodTorusProjection (rhombicPeriodPair t ht) w) :
    let z := (x : ℂ) + I*y
    ¬ ((X z 1 = 0 ∧ X z 2 = 0) ∨ (X z 0 = 0 ∧ X z 1 = 0)) := by
  let z := (x : ℂ) + I*y
  have hz : z ∉ (rhombicPeriodPair t ht).lattice :=
    rhombic_vertical_strip_not_mem ht ⟨by linarith [hx.1],hx.2⟩ hy
  have hcz : conj z ∉ (rhombicPeriodPair t ht).lattice := by
    intro h
    exact hz (by simpa using rhombic_conj_mem ht h)
  change ¬ ((X z 1 = 0 ∧ X z 2 = 0) ∨ (X z 0 = 0 ∧ X z 1 = 0))
  intro h
  rcases h with ⟨h1,h2⟩ | ⟨h0,h1⟩
  · have hh : X (conj z) = X z := by
      rw [hX.conjugation z hz]
      funext j
      fin_cases j
      · rfl
      · change -X z 1 = X z 1
        rw [h1,neg_zero]
      · change -X z 2 = X z 2
        rw [h2,neg_zero]
    have hfix := hXi _ hcz z hz hh
    obtain ⟨m,n,hr,hi⟩ := (rhombic_mem_lattice_iff ht _).mp ((periodTorusProjection_eq_iff _ _ _).mp hfix)
    simp only [Complex.sub_re,Complex.conj_re,sub_self,Complex.sub_im,Complex.conj_im,sub_neg_eq_add] at hr hi
    have hzim : z.im = y := by simp [z,Complex.mul_im]
    rw [hzim] at hi
    have hnr : (n : ℝ) = -2*(m : ℝ) := by linarith
    rw [hnr] at hi
    have hlo : (-2 : ℤ) < m := by exact_mod_cast (show (-2 : ℝ) < m by nlinarith [hy.2])
    have hhi : m < (0 : ℤ) := by exact_mod_cast (show (m : ℝ) < 0 by nlinarith [hy.1])
    have hm : m = -1 := by omega
    rw [hm] at hi
    norm_num at hi
    exact hn (by linarith)
  · have hh : X (-conj z) = X z := by
      rw [hX.neg _ hcz,hX.conjugation z hz]
      funext j
      fin_cases j
      · change -X z 0 = X z 0
        rw [h0,neg_zero]
      · change -X z 1 = X z 1
        rw [h1,neg_zero]
      · exact neg_neg _
    have hncz : -conj z ∉ (rhombicPeriodPair t ht).lattice := by simpa using hcz
    have hfix := hXi _ hncz z hz hh
    obtain ⟨n,hn⟩ := (rhombic_vertical_fixed_projection_iff ht z).mp hfix
    have hzre : z.re = x := by simp [z,Complex.mul_re]
    rw [hzre] at hn
    have hn0 : (0 : ℤ) < n := by exact_mod_cast (hn ▸ hx.1)
    have hn1 : n < (1 : ℤ) := by exact_mod_cast (hn ▸ hx.2)
    omega

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rectangle_boundary_derivatives_one_sign
#print axioms TwoAxisHelicoid.harmonic_embedded_rectangle_avoids_axes
