import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.Basic

namespace TwoAxisHelicoid
open Complex Metric Set Filter
open scoped Topology ComplexConjugate

abbrev complexUnitDisk : Set ℂ := ball 0 1

noncomputable def diskMobius (a z : ℂ) : ℂ := (z-a)/(1-conj a*z)

theorem diskMobius_den_ne {a z : ℂ} (ha : a ∈ complexUnitDisk) (hz : z ∈ complexUnitDisk) :
    1-conj a*z ≠ 0 := by
  intro h
  have h' := congrArg norm (sub_eq_zero.mp h)
  rw [norm_one,norm_mul,norm_conj] at h'
  have ha' : ‖a‖ < 1 := by simpa using ha
  have hz' : ‖z‖ < 1 := by simpa using hz
  nlinarith [mul_lt_mul_of_pos_right ha' (by positivity : 0 < (1:ℝ)),mul_le_mul_of_nonneg_left hz'.le (norm_nonneg a)]

theorem diskMobius_norm_identity (a z : ℂ) :
    normSq (1-conj a*z)-normSq (z-a) = (1-normSq a)*(1-normSq z) := by
  simp [Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
  ring

theorem diskMobius_mapsTo {a : ℂ} (ha : a ∈ complexUnitDisk) : MapsTo (diskMobius a) complexUnitDisk complexUnitDisk := by
  intro z hz
  have h1 : ‖a‖ < 1 := by simpa using ha
  have h2 : ‖z‖ < 1 := by simpa using hz
  have ha' : 1-normSq a > 0 := by rw [← Complex.sq_norm]; nlinarith [norm_nonneg a]
  have hz' : 1-normSq z > 0 := by rw [← Complex.sq_norm]; nlinarith [norm_nonneg z]
  have hh := diskMobius_norm_identity a z
  rw [← Complex.sq_norm,← Complex.sq_norm] at hh
  have hlt : ‖z-a‖ < ‖1-conj a*z‖ := by nlinarith [mul_pos ha' hz',norm_nonneg (z-a),norm_nonneg (1-conj a*z)]
  simpa [diskMobius,norm_div,div_lt_one (norm_pos_iff.mpr (diskMobius_den_ne ha hz))] using hlt

theorem diskMobius_analyticAt {a z : ℂ} (ha : a ∈ complexUnitDisk) (hz : z ∈ complexUnitDisk) :
    AnalyticAt ℂ (diskMobius a) z :=
  (analyticAt_id.sub analyticAt_const).div (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) (diskMobius_den_ne ha hz)

theorem diskMobius_neg_mem {a : ℂ} (ha : a ∈ complexUnitDisk) : -a ∈ complexUnitDisk := by simpa using ha

theorem diskMobius_inverse {a z : ℂ} (ha : a ∈ complexUnitDisk) (hz : z ∈ complexUnitDisk) :
    diskMobius (-a) (diskMobius a z) = z := by
  have h1 := diskMobius_den_ne ha hz
  have h2 := diskMobius_den_ne (diskMobius_neg_mem ha) (diskMobius_mapsTo ha hz)
  apply (div_eq_iff h2).mpr
  dsimp only [diskMobius]
  simp only [map_neg]
  generalize hd : (1-conj a*z) = d at *
  field_simp [h1]
  subst d
  ring

/-- The disk pseudohyperbolic distance is nonincreasing under each
holomorphic self-map; hence every disk biholomorphism preserves it. -/
theorem disk_holomorphic_distance_nonexpanding {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F complexUnitDisk) (hFD : MapsTo F complexUnitDisk complexUnitDisk)
    {a z : ℂ} (ha : a ∈ complexUnitDisk) (hz : z ∈ complexUnitDisk) :
    ‖diskMobius (F a) (F z)‖ ≤ ‖diskMobius a z‖ := by
  let g := diskMobius (F a) ∘ F ∘ diskMobius (-a)
  have hneg := diskMobius_neg_mem ha
  have hg : MapsTo g complexUnitDisk complexUnitDisk := (diskMobius_mapsTo (hFD ha)).comp (hFD.comp (diskMobius_mapsTo hneg))
  have ha' : AnalyticOnNhd ℂ g complexUnitDisk := by
    intro w hw
    have h := diskMobius_mapsTo hneg hw
    exact ((diskMobius_analyticAt (hFD ha) (hFD h)).comp (hF _ h)).comp (diskMobius_analyticAt hneg hw)
  have h0 : g 0 = 0 := by simp [g,diskMobius]
  have hd := Complex.norm_le_norm_of_mapsTo_ball ha'.differentiableOn
    (fun w hw => ball_subset_closedBall (hg hw)) h0
    (show ‖diskMobius a z‖ < 1 by simpa using diskMobius_mapsTo ha hz)
  simpa only [g,Function.comp_apply,diskMobius_inverse ha hz] using hd

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.disk_holomorphic_distance_nonexpanding
