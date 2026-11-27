import TwoAxisHelicoid.PdfAdaptiveChordCell
import TwoAxisHelicoid.PdfHorizontalIntegral
import TwoAxisHelicoid.JacobiChordCell

namespace TwoAxisHelicoid.PdfVertical
open Complex ComplexBall

/-- Keep the tighter endpoints of two verified enclosures of the same value. -/
def Grid.intersect (a b : Grid) : Grid :=
  ⟨max a.lo b.lo, min a.hi b.hi, a.ok && b.ok⟩

theorem Grid.contains_intersect {a b : Grid} {x : ℝ} (ha : a.Contains x) (hb : b.Contains x) :
    (a.intersect b).Contains x := by
  intro active
  obtain ⟨aa,bb⟩ := Bool.and_eq_true_iff.mp active
  obtain ⟨al,au⟩ := ha aa
  obtain ⟨bl,bu⟩ := hb bb
  change ((max a.lo b.lo : ℤ) : ℝ) ≤ _ ∧ _ ≤ ((min a.hi b.hi : ℤ) : ℝ)
  rw [Int.cast_max, Int.cast_min]
  exact ⟨max_le al bl, le_min au bu⟩

def CGrid.intersect (a b : CGrid) : CGrid :=
  ⟨a.re.intersect b.re, a.im.intersect b.im⟩

theorem CGrid.contains_intersect {a b : CGrid} {z : ℂ} (ha : a.Contains z) (hb : b.Contains z) :
    (a.intersect b).Contains z :=
  ⟨Grid.contains_intersect ha.1 hb.1, Grid.contains_intersect ha.2 hb.2⟩

def CGrid.ofBall (b : ComplexBall) : CGrid :=
  ⟨Grid.ofRats (b.center.re-b.radius) (b.center.re+b.radius),
   Grid.ofRats (b.center.im-b.radius) (b.center.im+b.radius)⟩

theorem CGrid.contains_ofBall {b : ComplexBall} {z : ℂ} (h : b.Contains z) : (ofBall b).Contains z :=
  ⟨Grid.contains_rats (re_bounds h).1 (re_bounds h).2,
   Grid.contains_rats (pdf_horizontal_imag_bounds h).1 (pdf_horizontal_imag_bounds h).2⟩

def CGrid.ofError (e : ℚ) : CGrid := ⟨Grid.ofRats (-e) e, Grid.ofRats (-e) e⟩

theorem CGrid.contains_ofError {e : ℚ} {z : ℂ} (small : ‖z‖ ≤ (e : ℝ)) :
    (ofError e).Contains z := by
  have re := abs_le.mp ((Complex.abs_re_le_norm z).trans small)
  have im := abs_le.mp ((Complex.abs_im_le_norm z).trans small)
  exact ⟨Grid.contains_rats (by simpa only [Rat.cast_neg] using re.1) re.2,
    Grid.contains_rats (by simpa only [Rat.cast_neg] using im.1) im.2⟩

def CGrid.finiteSum : (n : ℕ) → (Fin n → CGrid) → CGrid
  | 0, _ => CGrid.ofInt 0
  | n + 1, v => (v 0).add (finiteSum n (fun i => v i.succ))

theorem CGrid.contains_finiteSum {n : ℕ} {b : Fin n → CGrid} {v : Fin n → ℂ}
    (h : ∀ i, (b i).Contains (v i)) : (finiteSum n b).Contains (∑ i, v i) := by
  induction n with
  | zero =>
    simpa only [finiteSum, Finset.univ_eq_empty, Finset.sum_empty, Int.cast_zero] using CGrid.contains_ofInt 0
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    exact CGrid.contains_add (h 0) (ih (fun i => h i.succ))

def refinedWeightedChordNode (order : ℕ) (p : ChordParams) (s weight : ℚ)
    (old : ComplexBall) (refineNode : Bool) : CGrid :=
  if refineNode then
    (CGrid.ofBall old).intersect ((truncatedChordCell order p (Grid.ofRats s s)).scale (Grid.ofRats weight weight))
  else CGrid.ofBall old

theorem refinedWeightedChordNode_sound (order : ℕ) {p : ChordParams} {t a : ℝ} (hp : p.Sound t a)
    (ht : 0<t) (hu : t≤7/5) (s weight : ℚ) {old : ComplexBall} (refineNode : Bool)
    (oldBound : old.Contains ((weight:ℂ)*jacobiChordKernel t a (s:ℂ))) :
    (refinedWeightedChordNode order p s weight old refineNode).Contains
      ((weight:ℂ)*jacobiChordKernel t a (s:ℂ)) := by
  cases refineNode with
  | false => exact CGrid.contains_ofBall oldBound
  | true =>
    apply CGrid.contains_intersect (CGrid.contains_ofBall oldBound)
    have grid (r : ℚ) : (Grid.ofRats r r).Contains (r:ℝ) := Grid.contains_rats le_rfl le_rfl
    simpa only [Complex.ofReal_ratCast] using
      CGrid.contains_scale (grid weight) (truncatedChordCell_sound order hp (grid s) ht hu)

end TwoAxisHelicoid.PdfVertical

#print axioms TwoAxisHelicoid.PdfVertical.refinedWeightedChordNode_sound
#print axioms TwoAxisHelicoid.PdfVertical.CGrid.contains_finiteSum

