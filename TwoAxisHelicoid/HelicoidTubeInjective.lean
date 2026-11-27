import TwoAxisHelicoid.HelicoidTubeDifferential
import TwoAxisHelicoid.StripMapInjective

namespace TwoAxisHelicoid
open Real Set

theorem helicoidQ_continuous : Continuous helicoidQ := by
  unfold helicoidQ
  fun_prop

theorem helicoidAngle_continuous : Continuous (fun p : ℝ × ℝ => helicoidAngle p.2 p.1) := by
  unfold helicoidAngle
  exact (continuous_fst.mul continuous_snd).div
    (helicoidQ_continuous.comp continuous_snd) (fun p => (helicoidQ_pos p.2).ne')

theorem helicoidA_continuous : Continuous (fun p : ℝ × ℝ => helicoidA p.2 p.1) := by
  unfold helicoidA
  exact continuous_const.sub ((continuous_fst.pow 2).div
    ((helicoidQ_continuous.comp continuous_snd).pow 4) (fun p => pow_ne_zero _ (helicoidQ_pos p.2).ne'))

theorem helicoidUr_continuous : Continuous (fun p : ℝ × ℝ => helicoidUr p.2 p.1) :=
  helicoidA_continuous.mul (continuous_cos.comp helicoidAngle_continuous)

theorem helicoidVr_continuous : Continuous (fun p : ℝ × ℝ => helicoidVr p.2 p.1) :=
  helicoidA_continuous.neg.mul (continuous_sin.comp helicoidAngle_continuous)

theorem helicoidUs_continuous : Continuous (fun p : ℝ × ℝ => helicoidUs p.2 p.1) := by
  have hc : Continuous (fun p : ℝ × ℝ => p.1*p.2/(helicoidQ p.2)^2) :=
    (continuous_fst.mul continuous_snd).div
      ((helicoidQ_continuous.comp continuous_snd).pow 2) (fun p => pow_ne_zero _ (helicoidQ_pos p.2).ne')
  exact (hc.neg.mul (continuous_cos.comp helicoidAngle_continuous)).sub
    ((helicoidQ_continuous.comp continuous_snd).mul (continuous_sin.comp helicoidAngle_continuous))

theorem helicoidVs_continuous : Continuous (fun p : ℝ × ℝ => helicoidVs p.2 p.1) := by
  have hc : Continuous (fun p : ℝ × ℝ => p.1*p.2/(helicoidQ p.2)^2) :=
    (continuous_fst.mul continuous_snd).div
      ((helicoidQ_continuous.comp continuous_snd).pow 2) (fun p => pow_ne_zero _ (helicoidQ_pos p.2).ne')
  exact (hc.mul (continuous_sin.comp helicoidAngle_continuous)).sub
    ((helicoidQ_continuous.comp continuous_snd).mul (continuous_cos.comp helicoidAngle_continuous))

theorem helicoidU_surjective (s : ℝ) (hs : |s| < 1) :
    Function.Surjective (fun r => helicoidU r s) := by
  apply surjective_of_derivative_lower_bound (c := (1-s^2)/2)
  · have hs2 := (sq_lt_one_iff_abs_lt_one s).mpr hs
    positivity
  · exact fun r => helicoidU_r_hasDerivAt r s
  · exact fun r => helicoidUr_lower r s hs

theorem helicoid_reduced_map_injective {r₁ r₂ s₁ s₂ : ℝ}
    (hs₁ : |s₁| < 1) (hs₂ : |s₂| < 1)
    (hu : helicoidU r₁ s₁ = helicoidU r₂ s₂)
    (hv : helicoidV r₁ s₁ = helicoidV r₂ s₂) : r₁ = r₂ ∧ s₁ = s₂ := by
  have hinj := strip_map_injective (l := (-1:ℝ)) (h := (1:ℝ))
    (fun s r => helicoidU_s_hasDerivAt r s) (fun s r => helicoidU_r_hasDerivAt r s)
    (fun s r => helicoidV_s_hasDerivAt r s) (fun s r => helicoidV_r_hasDerivAt r s)
    helicoidUs_continuous helicoidUr_continuous helicoidVs_continuous helicoidVr_continuous
    (fun s hs r => helicoidUr_pos r s (abs_lt.mpr hs))
    (fun s hs => helicoidU_surjective s (abs_lt.mpr hs))
    (fun s hs r => helicoid_jacobian_neg r s (abs_lt.mpr hs))
  have he : (s₁,r₁) = (s₂,r₂) := hinj
    ⟨abs_lt.mp hs₁,mem_univ _⟩ ⟨abs_lt.mp hs₂,mem_univ _⟩ (Prod.ext hu hv)
  exact ⟨congrArg Prod.snd he,congrArg Prod.fst he⟩

/-- The standard helicoid plus signed distance times its unit normal.
The three coordinates are represented as a nested real product. -/
noncomputable def helicoidNormalMap (r θ s : ℝ) : ℝ × ℝ × ℝ :=
  (r*cos θ+s/helicoidQ r*sin θ,
   r*sin θ-s/helicoidQ r*cos θ,
   θ+helicoidAngle r s)

theorem helicoidNormalMap_reduce (r θ s : ℝ) :
    let p := helicoidNormalMap r θ s
    (p.1*cos p.2.2+p.2.1*sin p.2.2,
      -p.1*sin p.2.2+p.2.1*cos p.2.2) = (helicoidU r s,helicoidV r s) := by
  dsimp [helicoidNormalMap,helicoidU,helicoidV]
  rw [sin_add,cos_add]
  apply Prod.ext
  · calc
      _ = r*cos (helicoidAngle r s)*(sin θ^2+cos θ^2)-
          s/helicoidQ r*sin (helicoidAngle r s)*(sin θ^2+cos θ^2) := by ring
      _ = _ := by rw [sin_sq_add_cos_sq]; ring
  · calc
      _ = -r*sin (helicoidAngle r s)*(sin θ^2+cos θ^2)-
          s/helicoidQ r*cos (helicoidAngle r s)*(sin θ^2+cos θ^2) := by ring
      _ = _ := by rw [sin_sq_add_cos_sq]; ring

/-- Global injectivity on the full width-one normal strip, as in PDF §4.2. -/
theorem helicoidNormalMap_injective {r₁ r₂ θ₁ θ₂ s₁ s₂ : ℝ}
    (hs₁ : |s₁| < 1) (hs₂ : |s₂| < 1)
    (he : helicoidNormalMap r₁ θ₁ s₁ = helicoidNormalMap r₂ θ₂ s₂) :
    r₁ = r₂ ∧ θ₁ = θ₂ ∧ s₁ = s₂ := by
  have hred : (helicoidU r₁ s₁,helicoidV r₁ s₁) =
      (helicoidU r₂ s₂,helicoidV r₂ s₂) := by
    rw [← helicoidNormalMap_reduce r₁ θ₁ s₁,← helicoidNormalMap_reduce r₂ θ₂ s₂]
    rw [he]
  obtain ⟨hr,hs⟩ := helicoid_reduced_map_injective hs₁ hs₂
    (congrArg Prod.fst hred) (congrArg Prod.snd hred)
  have hz := congrArg (fun p : ℝ × ℝ × ℝ => p.2.2) he
  change θ₁+helicoidAngle r₁ s₁ = θ₂+helicoidAngle r₂ s₂ at hz
  rw [hr,hs] at hz
  exact ⟨hr,add_right_cancel hz,hs⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoidNormalMap_injective
