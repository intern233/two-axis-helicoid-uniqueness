import TwoAxisHelicoid.PdfAdaptiveChordCell
import TwoAxisHelicoid.PdfChordIntegralSound

namespace TwoAxisHelicoid.PdfVertical
open Complex MeasureTheory Set

/-- Integration of a coordinate of a continuous curve preserves its interval
enclosure after multiplication by the width of the interval. -/
private theorem coordinate_integral_grid (L : ℂ →L[ℝ] ℝ) {f : ℝ → ℂ}
    (cont : Continuous f) {l u : ℝ} (lt : l<u) {b width : Grid}
    (bound : ∀ x∈Icc l u, b.Contains (L (f x))) (w : width.Contains (u-l)) :
    (width.mul b).Contains (L (∫ x : ℝ in l..u, f x)) := by
  let D := (Grid.denom:ℝ)
  have integrable := (continuous_const.mul (L.continuous.comp cont) :
    Continuous (fun x => D*L (f x))).intervalIntegrable l u (μ:=volume)
  have mean : b.Contains ((∫ x in l..u, L (f x))/(u-l)) := by
    intro ok
    have low := intervalIntegral.integral_mono_on (μ:=volume) lt.le intervalIntegrable_const integrable
      (fun x hx => (bound x hx ok).1)
    have high := intervalIntegral.integral_mono_on (μ:=volume) lt.le integrable intervalIntegrable_const
      (fun x hx => (bound x hx ok).2)
    change (∫ _ : ℝ in l..u, (b.lo:ℝ))≤∫ x in l..u, D*L (f x) at low
    change (∫ x in l..u, D*L (f x))≤∫ _ : ℝ in l..u, (b.hi:ℝ) at high
    simp only [intervalIntegral.integral_const,intervalIntegral.integral_const_mul,smul_eq_mul] at low high
    change (b.lo:ℝ)≤D*((∫ x in l..u, L (f x))/(u-l)) ∧ D*((∫ x in l..u, L (f x))/(u-l))≤(b.hi:ℝ)
    rw [← mul_div_assoc,le_div_iff₀ (sub_pos.mpr lt),div_le_iff₀ (sub_pos.mpr lt)]
    exact ⟨(mul_comm _ _).le.trans low,high.trans (mul_comm _ _).le⟩
  have result := Grid.contains_mul w mean
  rwa [mul_comm (u-l),div_mul_cancel₀ _ (sub_ne_zero.mpr lt.ne'),
    L.intervalIntegral_comp_comm (cont.intervalIntegrable l u (μ:=volume))] at result

/-- Each certified path encloses the genuine complex integral. The recursion
checks the orientation and adjacency of every segment of the same contour. -/
theorem AdaptiveChordPath.integral {N : ℕ} {p : ChordParams} {t a : ℝ}
    (data : p.Sound t a) (ht : 0<t) (hu : t≤7/5) (path : AdaptiveChordPath)
    (valid : path.checked N p=true) : path.output.Contains
      (∫ x : ℝ in (path.lower:ℝ)..(path.upper:ℝ),jacobiChordKernel t a (x:ℂ)) := by
  let f := fun x : ℝ => jacobiChordKernel t a (x:ℂ)
  have c : Continuous f := jacobiChordKernel_continuous_real ht (leftNome_lt_one_third ht hu).le a
  induction path with
  | edge l u b =>
    obtain ⟨lt,output⟩ := of_decide_eq_true valid
    change b.Contains (∫ x in (l:ℝ)..(u:ℝ),f x)
    rw [← output]
    have cells (x : ℝ) (hx : x∈Icc (l:ℝ) (u:ℝ)) := truncatedChordCell_sound N data
      (Grid.contains_rats hx.1 hx.2) ht hu
    have width : (Grid.ofRats (u-l) (u-l)).Contains ((u:ℝ)-l) := by
      simpa only [Rat.cast_sub] using (Grid.contains_rats (a:=u-l) (b:=u-l) le_rfl le_rfl)
    exact ⟨coordinate_integral_grid Complex.reCLM c (Rat.cast_lt.mpr lt) (fun x hx => (cells x hx).1) width,
      coordinate_integral_grid Complex.imCLM c (Rat.cast_lt.mpr lt) (fun x hx => (cells x hx).2) width⟩
  | join left right b ihl ihr =>
    simp only [checked,Bool.and_eq_true,decide_eq_true_eq] at valid
    obtain ⟨⟨hl,hr⟩,adj,join⟩ := valid
    have leftBound := ihl hl
    have rightBound := ihr hr
    rw [adj] at leftBound
    have eqn := intervalIntegral.integral_add_adjacent_intervals
      (c.intervalIntegrable (left.lower:ℝ) (right.lower:ℝ) (μ:=volume))
      (c.intervalIntegrable (right.lower:ℝ) (right.upper:ℝ) (μ:=volume))
    change b.Contains (∫ x in (left.lower:ℝ)..(right.upper:ℝ),f x)
    rw [← join,← eqn]
    exact CGrid.contains_add leftBound rightBound

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.AdaptiveChordPath.integral
