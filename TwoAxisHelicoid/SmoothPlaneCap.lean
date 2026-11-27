import TwoAxisHelicoid.HelicoidSphereCap
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic

namespace TwoAxisHelicoid
open Real Set
open scoped ContDiff
set_option maxHeartbeats 1000000

noncomputable def planeCapSwitch (A q : ℝ) : ℝ := smoothTransition (q-A)
noncomputable def planeCapScale (A H q : ℝ) : ℝ :=
  1-planeCapSwitch A q+planeCapSwitch A q*H/(1+q)
noncomputable def planeCapHeight (A H q : ℝ) : ℝ :=
  H*(planeCapSwitch A q*(q/(1+q)))

theorem planeCapSwitch_zero {A q : ℝ} (hq : q ≤ A) : planeCapSwitch A q = 0 :=
  smoothTransition.zero_of_nonpos (sub_nonpos.mpr hq)

theorem planeCapSwitch_one {A q : ℝ} (hq : A+1 ≤ q) : planeCapSwitch A q = 1 :=
  smoothTransition.one_of_one_le (by linarith)

theorem planeCapSwitch_nonneg (A q : ℝ) : 0 ≤ planeCapSwitch A q :=
  smoothTransition.nonneg _

theorem planeCapSwitch_le_one (A q : ℝ) : planeCapSwitch A q ≤ 1 :=
  smoothTransition.le_one _

theorem planeCapSwitch_pos {A q : ℝ} (hq : A < q) : 0 < planeCapSwitch A q :=
  smoothTransition.pos_of_pos (sub_pos.mpr hq)

theorem planeCapSwitch_monotone (A : ℝ) : Monotone (planeCapSwitch A) :=
  fun _ _ h => smoothTransition.monotone (sub_le_sub_right h A)

theorem planeCapScale_of_le {A H q : ℝ} (hq : q ≤ A) : planeCapScale A H q = 1 := by
  simp [planeCapScale,planeCapSwitch_zero hq]

theorem planeCapHeight_of_le {A H q : ℝ} (hq : q ≤ A) : planeCapHeight A H q = 0 := by
  simp [planeCapHeight,planeCapSwitch_zero hq]

theorem planeCapScale_pos {A H q : ℝ} (hH : 0 < H) (hq : 0 ≤ q) :
    0 < planeCapScale A H q := by
  by_cases hc : planeCapSwitch A q = 0
  · simp [planeCapScale,hc]
  · have hcpos : 0 < planeCapSwitch A q := lt_of_le_of_ne (planeCapSwitch_nonneg A q) (Ne.symm hc)
    exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr (planeCapSwitch_le_one A q))
      (div_pos (mul_pos hcpos hH) (by linarith))

theorem planeCapHeight_pos {A H q : ℝ} (hA : 0 ≤ A) (hH : 0 < H) (hq : A < q) :
    0 < planeCapHeight A H q := by
  have hq0 : 0 < q := hA.trans_lt hq
  exact mul_pos hH (mul_pos (planeCapSwitch_pos hq) (div_pos hq0 (by linarith)))

theorem planeCapHeight_lt {A H q : ℝ} (hH : 0 < H) (hq : 0 ≤ q) :
    planeCapHeight A H q < H := by
  have hden : 0 < 1+q := by linarith
  have hfrac : q/(1+q) < 1 := (div_lt_one hden).mpr (by linarith)
  have hbound : planeCapSwitch A q*(q/(1+q)) ≤ q/(1+q) :=
    mul_le_of_le_one_left (div_nonneg hq hden.le) (planeCapSwitch_le_one A q)
  exact (mul_lt_mul_of_pos_left (hbound.trans_lt hfrac) hH).trans_eq (mul_one H)

theorem planeCapHeight_strictMonoOn {A H : ℝ} (hA : 0 ≤ A) (hH : 0 < H) :
    StrictMonoOn (planeCapHeight A H) (Ioi A) := by
  intro q hq r hr hqr
  have hq0 : 0 < q := hA.trans_lt hq
  have hr0 : 0 < r := hA.trans_lt hr
  have hfrac : q/(1+q) < r/(1+r) := by
    apply (div_lt_div_iff₀ (by linarith : 0 < 1+q) (by linarith : 0 < 1+r)).mpr
    nlinarith
  have h1 := mul_lt_mul_of_pos_left hfrac (planeCapSwitch_pos hq)
  have h2 := mul_le_mul_of_nonneg_right (planeCapSwitch_monotone A hqr.le)
    (div_nonneg hr0.le (by linarith : 0 ≤ 1+r))
  exact mul_lt_mul_of_pos_left (h1.trans_le h2) hH

/-- A smooth cap of the whole plane. It fixes the disk of squared radius
`A`, and outside the next annulus is exactly a stereographic sphere with
one point missing. The positive height separates the turned-back part
of the cap from the fixed planar disk. -/
noncomputable def smoothPlaneCap (A H : ℝ) (p : ℝ × ℝ) : HelicoidTubeCoordinates :=
  let q := p.1^2+p.2^2
  ((planeCapScale A H q*p.1,planeCapHeight A H q),planeCapScale A H q*p.2)

theorem smoothPlaneCap_contDiff (A H : ℝ) : ContDiff ℝ (∞ : WithTop ℕ∞) (smoothPlaneCap A H) := by
  unfold smoothPlaneCap planeCapScale planeCapHeight planeCapSwitch
  dsimp only
  fun_prop (disch := intros; positivity)

theorem smoothPlaneCap_of_le {A H : ℝ} {p : ℝ × ℝ} (hp : p.1^2+p.2^2 ≤ A) :
    smoothPlaneCap A H p = ((p.1,0),p.2) := by
  simp [smoothPlaneCap,planeCapScale_of_le hp,planeCapHeight_of_le hp]

theorem smoothPlaneCap_injective {A H : ℝ} (hA : 0 ≤ A) (hH : 0 < H) :
    Function.Injective (smoothPlaneCap A H) := by
  intro p r he
  have hh : planeCapHeight A H (p.1^2+p.2^2) = planeCapHeight A H (r.1^2+r.2^2) :=
    congrArg (fun y : HelicoidTubeCoordinates => y.1.2) he
  by_cases hp : p.1^2+p.2^2 ≤ A
  · by_cases hr : r.1^2+r.2^2 ≤ A
    · rw [smoothPlaneCap_of_le hp,smoothPlaneCap_of_le hr] at he
      exact Prod.ext (congrArg (fun y : HelicoidTubeCoordinates => y.1.1) he)
        (congrArg (fun y : HelicoidTubeCoordinates => y.2) he)
    · have hpos := planeCapHeight_pos hA hH (lt_of_not_ge hr)
      rw [planeCapHeight_of_le hp] at hh
      exact False.elim (hpos.ne' hh.symm)
  · by_cases hr : r.1^2+r.2^2 ≤ A
    · have hpos := planeCapHeight_pos hA hH (lt_of_not_ge hp)
      rw [planeCapHeight_of_le hr] at hh
      exact False.elim (hpos.ne' hh)
    · have hq := (planeCapHeight_strictMonoOn hA hH).injOn
        (lt_of_not_ge hp) (lt_of_not_ge hr) hh
      have hscale := (planeCapScale_pos (A := A) hH
        (add_nonneg (sq_nonneg p.1) (sq_nonneg p.2))).ne'
      have hx := congrArg (fun y : HelicoidTubeCoordinates => y.1.1) he
      have hz := congrArg (fun y : HelicoidTubeCoordinates => y.2) he
      change planeCapScale A H (p.1^2+p.2^2)*p.1 = planeCapScale A H (r.1^2+r.2^2)*r.1 at hx
      change planeCapScale A H (p.1^2+p.2^2)*p.2 = planeCapScale A H (r.1^2+r.2^2)*r.2 at hz
      rw [← hq] at hx hz
      exact Prod.ext (mul_left_cancel₀ hscale hx) (mul_left_cancel₀ hscale hz)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.smoothPlaneCap_contDiff
#print axioms TwoAxisHelicoid.smoothPlaneCap_injective
