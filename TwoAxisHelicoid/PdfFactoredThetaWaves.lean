import TwoAxisHelicoid.PdfFactoredThetaAtoms

namespace TwoAxisHelicoid.PdfVertical
open Complex
open scoped ComplexConjugate

noncomputable def sampleThetaArgument (t a x : ℝ) (shifted : Bool) : ℂ :=
  Real.pi*(((x:ℂ)+I*((t/2:ℝ):ℂ))-(if shifted then (a:ℂ) else 0))/2

noncomputable def frequencyPlus (t a x : ℝ) (n : ℕ) (shifted : Bool) : ℂ :=
  ((Real.exp (-(Real.pi*t)*(waveExponentFactor n 1:ℝ)):ℝ):ℂ)*wavePhase n x*
    (if shifted then conj (wavePhase n a) else 1)

noncomputable def frequencyMinus (t a x : ℝ) (n : ℕ) (shifted : Bool) : ℂ :=
  ((Real.exp (-(Real.pi*t)*(waveExponentFactor n (-1):ℝ)):ℝ):ℂ)*conj (wavePhase n x)*
    (if shifted then wavePhase n a else 1)

theorem factored_frequency_identities (t a x : ℝ) (n : ℕ) (s : Bool) :
    frequencyPlus t a x n s=(Real.exp (-Real.pi*t*n*(n+1)/2):ℂ)*
      Complex.exp ((2*n+1:ℂ)*sampleThetaArgument t a x s*I) ∧
    frequencyMinus t a x n s=(Real.exp (-Real.pi*t*n*(n+1)/2):ℂ)*
      Complex.exp (-((2*n+1:ℂ)*sampleThetaArgument t a x s)*I) := by
  have ctwo : conj (2:ℂ)=2 := Complex.conj_ofReal 2
  cases s <;> constructor <;>
    simp [frequencyPlus,frequencyMinus,wavePhase,waveAngle,waveExponentFactor,sampleThetaArgument,
      ← Complex.exp_conj, Complex.ofReal_exp, ← Complex.exp_add] <;>
    congr 1 <;> ring_nf <;> norm_num [Complex.I_sq,ctwo] <;> ring

def FactoredFrequency.waves (p : FactoredFrequency) (node : CGrid) (shifted : Bool) : CGrid × CGrid :=
  let pos := node.scale p.plus
  let neg := node.reflected.scale p.minus
  if shifted then (pos.mul p.shift.reflected, neg.mul p.shift) else (pos,neg)

theorem FactoredFrequency.waves_sound {p : FactoredFrequency} {t a x : ℝ} {n : ℕ} (good : p.Sound t a n)
    {node : CGrid} (hn : node.Contains (wavePhase n x)) (s : Bool) :
    (p.waves node s).1.Contains (frequencyPlus t a x n s) ∧
    (p.waves node s).2.Contains (frequencyMinus t a x n s) := by
  have hp := CGrid.contains_scale good.1 hn
  have hm := CGrid.contains_scale good.2.1 (CGrid.contains_reflected hn)
  cases s
  · simpa only [waves,frequencyPlus,frequencyMinus,Bool.false_eq_true,ite_false,mul_one] using And.intro hp hm
  · exact ⟨CGrid.contains_mul hp (CGrid.contains_reflected good.2.2), CGrid.contains_mul hm good.2.2⟩

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.factored_frequency_identities

