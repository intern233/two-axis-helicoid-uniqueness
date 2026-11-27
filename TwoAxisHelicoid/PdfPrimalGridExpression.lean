import TwoAxisHelicoid.PdfComplexGridExp
import TwoAxisHelicoid.DyadicThetaTerm

namespace TwoAxisHelicoid.PdfVertical

def threeCGrids (a b c : CGrid) : ℕ → CGrid
  | 0 => a
  | 1 => b
  | 2 => c
  | _+3 => CGrid.ofInt 0

theorem threeCGrids_contains {A B C : CGrid} {a b c : ℂ}
    (ha : A.Contains a) (hb : B.Contains b) (hc : C.Contains c) :
    ∀ n, (threeCGrids A B C n).Contains (threeValues a b c n) := by
  intro n
  rcases n with _ | (_ | (_ | n))
  · exact ha
  · exact hb
  · exact hc
  · simpa only [threeCGrids,threeValues,Int.cast_zero] using CGrid.contains_ofInt 0

def expressionGrid (env : ℕ → CGrid) : BallExpression → CGrid
  | .const c => ⟨Grid.ofRats c.re c.re, Grid.ofRats c.im c.im⟩
  | .pi => CGrid.real Grid.pi
  | .input i => env i
  | .add a b => (expressionGrid env a).add (expressionGrid env b)
  | .neg a => (expressionGrid env a).neg
  | .mul a b => (expressionGrid env a).mul (expressionGrid env b)
  | .inv a => (expressionGrid env a).inv
  | .exp a => (expressionGrid env a).exp

theorem expressionGrid_contains {B : ℕ → CGrid} {v : ℕ → ℂ} (h : ∀ i, (B i).Contains (v i))
    (e : BallExpression) : (expressionGrid B e).Contains (e.value v) := by
  induction e with
  | const c => exact ⟨Grid.contains_rats le_rfl le_rfl,Grid.contains_rats le_rfl le_rfl⟩
  | pi => exact CGrid.contains_real Grid.contains_pi
  | input i => exact h i
  | add _ _ ia ib => exact CGrid.contains_add ia ib
  | neg _ ia => exact CGrid.contains_neg ia
  | mul _ _ ia ib => exact CGrid.contains_mul ia ib
  | inv _ ia => exact CGrid.contains_inv ia
  | exp _ ia => exact CGrid.contains_exp ia

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.expressionGrid_contains
