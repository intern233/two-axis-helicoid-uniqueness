import TwoAxisHelicoid.QuadratureRule
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.Basic

namespace TwoAxisHelicoid
open Set Complex MeasureTheory

/-- Along a horizontal segment the reflected term uses the same
positive half-length after reversal. A pair of real linear
observables of the two complex means integrates the actual rate. -/
theorem spatial_paired_horizontal_means {f : ℂ → ℂ} (A B : ℂ →L[ℝ] ℝ) (c : ℂ) (h : ℝ)
    (cp : ContinuousOn (fun u : ℝ => f (c+(h:ℂ)*u)) (Icc (-1:ℝ) 1))
    (cm : ContinuousOn (fun u : ℝ => f (-c+(h:ℂ)*u)) (Icc (-1:ℝ) 1))
    {u : ℝ → ℝ} (rate : ∀ x∈Icc (-1:ℝ) 1,
      HasDerivAt u (h*(A (f (c+(h:ℂ)*x))+B (f (-(c+(h:ℂ)*x))))) x) :
    u 1-u (-1)=2*h*(A (normalizedIntegral f c h)+B (normalizedIntegral f (-c) h)) := by
  let P := fun x : ℝ => f (c+(h:ℂ)*x)
  let N := fun x : ℝ => f (-c+(h:ℂ)*x)
  let negN := fun x : ℝ => N (-x)
  have refl (x : ℝ) : f (-(c+(h:ℂ)*x))=negN x := by
    apply congrArg f
    push_cast
    ring
  have m : (-1:ℝ)≤1 := by norm_num
  have cn : ContinuousOn negN (Icc (-1:ℝ) 1) :=
    cm.comp continuous_neg.continuousOn fun t ht => ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have pI : IntervalIntegrable P volume (-1) 1 := cp.intervalIntegrable_of_Icc m
  have nI : IntervalIntegrable negN volume (-1) 1 := cn.intervalIntegrable_of_Icc m
  have aI : IntervalIntegrable (fun x => A (P x)) volume (-1) 1 := (A.continuous.comp_continuousOn cp).intervalIntegrable_of_Icc m
  have bI : IntervalIntegrable (fun x => B (negN x)) volume (-1) 1 := (B.continuous.comp_continuousOn cn).intervalIntegrable_of_Icc m
  have FTC : (∫ x : ℝ in (-1)..1, h*(A (P x)+B (negN x)))=u 1-u (-1) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => by simpa only [P,← refl] using rate x ((uIcc_of_le m) ▸ hx)) ((aI.add bI).const_mul h)
  have inv : (∫ x : ℝ in (-1)..1, negN x)=∫ x : ℝ in (-1)..1, N x := by
    dsimp only [negN]
    rw [intervalIntegral.integral_comp_neg,neg_neg]
  have half (L : ℂ →L[ℝ] ℝ) (v : ℂ) : L ((1/2:ℂ)*v)=(1/2:ℝ)*L v := by
    have eq : (1/2:ℂ)*v=(1/2:ℝ) • v := by simp [Complex.real_smul]
    rw [eq,map_smul,smul_eq_mul]
  rw [← FTC,intervalIntegral.integral_const_mul,intervalIntegral.integral_add aI bI,
    A.intervalIntegral_comp_comm pI,B.intervalIntegral_comp_comm nI,inv,normalizedIntegral,normalizedIntegral,half,half]
  dsimp [P,N]
  ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.spatial_paired_horizontal_means
