import TwoAxisHelicoid.PdfPrimalGridKernel
import TwoAxisHelicoid.PdfQuadratureNodeGrid

namespace TwoAxisHelicoid.PdfVertical
open Complex
open scoped ComplexConjugate

def Grid.expWide (x : Grid) : Grid :=
  (((x.divNat 8).exp.squared).squared).squared

theorem Grid.contains_expWide {g : Grid} {x : ℝ} (hx : g.Contains x) :
    g.expWide.Contains (Real.exp x) := by
  have b := Grid.contains_squared (Grid.contains_squared (Grid.contains_squared
    (Grid.contains_exp (Grid.contains_divNat (n:=8) hx))))
  have e : ((Real.exp (x/(8:ℕ))^2)^2)^2=Real.exp x := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [e] at b
  exact b

def CGrid.reflected (g : CGrid) : CGrid := ⟨g.re,g.im.neg⟩

theorem CGrid.contains_reflected {g : CGrid} {z : ℂ} (hz : g.Contains z) :
    g.reflected.Contains (conj z) :=
  ⟨hz.1, Grid.contains_neg hz.2⟩

def waveExponentFactor (n : ℕ) (s : ℚ) : ℚ :=
  (n:ℚ)*(n+1)/2+s*(2*n+1)/4

noncomputable def waveAngle (n : ℕ) (x : ℝ) : ℝ := Real.pi*x*(2*n+1)/2

noncomputable def wavePhase (n : ℕ) (x : ℝ) : ℂ := Complex.exp ((waveAngle n x:ℂ)*I)

def wavePhaseGrid (n : ℕ) (x : Grid) : CGrid :=
  CGrid.trigBox (((Grid.pi.mul x).mul (Grid.ofInt (2*(n:ℤ)+1))).divNat 2)

theorem wavePhaseGrid_sound (n : ℕ) {X : Grid} {x : ℝ} (hx : X.Contains x) :
    (wavePhaseGrid n X).Contains (wavePhase n x) := by
  have b := CGrid.trigBox_contains (Grid.contains_divNat (n:=2)
    (Grid.contains_mul (Grid.contains_mul Grid.contains_pi hx) (Grid.contains_int (2*(n:ℤ)+1))))
  simpa only [wavePhaseGrid, wavePhase, waveAngle, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
    Int.cast_natCast, Int.cast_one, Nat.cast_ofNat] using b

def waveWeightGrid (n : ℕ) (s : ℚ) (T : Grid) : Grid :=
  let c := waveExponentFactor n s
  (((Grid.pi.mul T).neg).mul (Grid.ofRats c c)).expWide

theorem waveWeightGrid_sound (n : ℕ) (s : ℚ) {T : Grid} {t : ℝ} (ht : T.Contains t) :
    (waveWeightGrid n s T).Contains (Real.exp (-(Real.pi*t)*(waveExponentFactor n s:ℝ))) :=
  Grid.contains_expWide (Grid.contains_mul (Grid.contains_neg (Grid.contains_mul Grid.contains_pi ht))
    (Grid.contains_rats le_rfl le_rfl))

structure FactoredFrequency where
  plus : Grid
  minus : Grid
  shift : CGrid

def FactoredFrequency.build (T A : Grid) (n : ℕ) : FactoredFrequency :=
  ⟨waveWeightGrid n 1 T, waveWeightGrid n (-1) T, wavePhaseGrid n A⟩

def FactoredFrequency.Sound (p : FactoredFrequency) (t a : ℝ) (n : ℕ) : Prop :=
  p.plus.Contains (Real.exp (-(Real.pi*t)*(waveExponentFactor n 1:ℝ))) ∧
  p.minus.Contains (Real.exp (-(Real.pi*t)*(waveExponentFactor n (-1):ℝ))) ∧
  p.shift.Contains (wavePhase n a)

theorem FactoredFrequency.build_sound {T A : Grid} {t a : ℝ} (ht : T.Contains t)
    (ha : A.Contains a) (n : ℕ) : (FactoredFrequency.build T A n).Sound t a n :=
  ⟨waveWeightGrid_sound n 1 ht, waveWeightGrid_sound n (-1) ht, wavePhaseGrid_sound n ha⟩

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.FactoredFrequency.build_sound

