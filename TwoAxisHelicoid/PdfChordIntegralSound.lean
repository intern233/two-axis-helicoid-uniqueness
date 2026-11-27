import TwoAxisHelicoid.PdfChordCellSound
import TwoAxisHelicoid.PdfChordQuadrature
import TwoAxisHelicoid.PdfHorizontalIntegral
import TwoAxisHelicoid.PdfVerticalRowSound

namespace TwoAxisHelicoid.PdfVertical
open Complex MeasureTheory Set

/-- The average of a continuous real function stays in a closed grid
interval enclosing it on a nondegenerate segment. -/
private theorem grid_integral_average {B : Grid} {f : ℝ → ℝ} (cont : Continuous f) {l u : ℝ}
    (lt : l<u) (enclosure : ∀ x∈Icc l u,B.Contains (f x)) :
    B.Contains ((∫ x in l..u, f x)/(u-l)) := by
  intro ok
  let D := (Grid.denom:ℝ)
  have integrable := (continuous_const.mul cont : Continuous (fun x => D*f x)).intervalIntegrable l u (μ:=volume)
  have low := intervalIntegral.integral_mono_on (μ:=volume) lt.le intervalIntegrable_const integrable
    (fun x hx => (enclosure x hx ok).1)
  have high := intervalIntegral.integral_mono_on (μ:=volume) lt.le integrable intervalIntegrable_const
    (fun x hx => (enclosure x hx ok).2)
  change (∫ _ : ℝ in l..u, (B.lo:ℝ))≤∫ x in l..u, D*f x at low
  change (∫ x in l..u, D*f x)≤∫ _ : ℝ in l..u, (B.hi:ℝ) at high
  simp only [intervalIntegral.integral_const,intervalIntegral.integral_const_mul,smul_eq_mul] at low high
  change (B.lo:ℝ)≤D*((∫ x in l..u,f x)/(u-l)) ∧ D*((∫ x in l..u,f x)/(u-l))≤(B.hi:ℝ)
  rw [← mul_div_assoc,le_div_iff₀ (sub_pos.mpr lt),div_le_iff₀ (sub_pos.mpr lt)]
  exact ⟨(mul_comm _ _).le.trans low,high.trans (mul_comm _ _).le⟩

private theorem grid_integral_cell {B W : Grid} {f : ℝ → ℂ} (cont : Continuous f) {l u : ℝ}
    (lt : l<u) (enclosure : ∀ x∈Icc l u,B.Contains (f x).re) (width : W.Contains (u-l)) :
    (W.mul B).Contains (∫ x in l..u,f x).re := by
  have avg := grid_integral_average (Complex.continuous_re.comp cont) lt enclosure
  have e : (u-l)*((∫ x in l..u,(f x).re)/(u-l))=(∫ x in l..u,f x).re := by
    rw [mul_comm (u-l),div_mul_cancel₀ _ (sub_ne_zero.mpr lt.ne')]
    exact intervalIntegral.intervalIntegral_re (cont.intervalIntegrable l u (μ:=volume))
  rw [← e]
  exact Grid.contains_mul width avg

private theorem grid_integral_imag_cell {B W : Grid} {f : ℝ → ℂ} (cont : Continuous f) {l u : ℝ}
    (lt : l<u) (enclosure : ∀ x∈Icc l u,B.Contains (f x).im) (width : W.Contains (u-l)) :
    (W.mul B).Contains (∫ x in l..u,f x).im := by
  have avg := grid_integral_average (Complex.continuous_im.comp cont) lt enclosure
  have e : (u-l)*((∫ x in l..u,(f x).im)/(u-l))=(∫ x in l..u,f x).im := by
    rw [mul_comm (u-l),div_mul_cancel₀ _ (sub_ne_zero.mpr lt.ne')]
    exact intervalIntegral.intervalIntegral_im (cont.intervalIntegrable l u (μ:=volume))
  rw [← e]
  exact Grid.contains_mul width avg

theorem chordSpan_sound {par : ChordParams} {t a : ℝ} (data : par.Sound t a) (ht : 0<t) (hu : t≤7/5)
    (d : ℕ) {l u : ℚ} (lt : l<u) :
    (chordSpan par d l u).Contains (∫ x : ℝ in (l:ℝ)..(u:ℝ),jacobiChordKernel t a (x:ℂ)) := by
  let f := fun x : ℝ => jacobiChordKernel t a (x:ℂ)
  have cont : Continuous f := jacobiChordKernel_continuous_real ht (leftNome_lt_one_third ht hu).le a
  induction d generalizing u l with
  | zero =>
    have cells (x : ℝ) (hx : x∈Icc (l:ℝ) (u:ℝ)) := chordCellValue_sound data
      (Grid.contains_rats hx.1 hx.2) ht hu
    have width : (Grid.ofRats (u-l) (u-l)).Contains ((u:ℝ)-l) := by
      simpa only [Rat.cast_sub] using (Grid.contains_rats (a:=u-l) (b:=u-l) le_rfl le_rfl)
    exact ⟨grid_integral_cell cont (Rat.cast_lt.mpr lt) (fun x hx => (cells x hx).1) width,
      grid_integral_imag_cell cont (Rat.cast_lt.mpr lt) (fun x hx => (cells x hx).2) width⟩
  | succ n ih =>
    let m := (l+u)/2
    have left : l<m := by dsimp [m];linarith
    have right : m<u := by dsimp [m];linarith
    have L := ih left
    have U := ih right
    have adj := intervalIntegral.integral_add_adjacent_intervals
      (cont.intervalIntegrable (l:ℝ) (m:ℝ) (μ:=volume)) (cont.intervalIntegrable (m:ℝ) (u:ℝ) (μ:=volume))
    rw [← adj]
    exact CGrid.contains_add L U

theorem chordTiles_sound {par : ChordParams} {t a : ℝ} (data : par.Sound t a) (ht : 0<t) (hu : t≤7/5)
    (last l : ℚ) (tiles : List (ℚ × ℕ)) :
    (chordTiles par last l tiles).Contains (∫ x : ℝ in (l:ℝ)..(last:ℝ),jacobiChordKernel t a (x:ℂ)) := by
  induction tiles generalizing l with
  | nil =>
    apply CGrid.contains_guard
    intro eqn
    have eq : l=last := of_decide_eq_true eqn
    rw [eq,intervalIntegral.integral_same]
    simpa only [Int.cast_zero] using CGrid.contains_ofInt 0
  | cons ud rest ih =>
    obtain ⟨u,d⟩ := ud
    apply CGrid.contains_guard
    intro good
    have cont := jacobiChordKernel_continuous_real ht (leftNome_lt_one_third ht hu).le a
    have adj := intervalIntegral.integral_add_adjacent_intervals
      (cont.intervalIntegrable (l:ℝ) (u:ℝ) (μ:=volume)) (cont.intervalIntegrable (u:ℝ) (last:ℝ) (μ:=volume))
    rw [← adj]
    exact CGrid.contains_add (chordSpan_sound data ht hu d (of_decide_eq_true good)) (ih u)

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.chordTiles_sound

