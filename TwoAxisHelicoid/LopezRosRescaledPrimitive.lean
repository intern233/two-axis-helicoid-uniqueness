import TwoAxisHelicoid.EnneperTransverseDoublePoint
import TwoAxisHelicoid.LopezRosEnneperNormalization
import Mathlib.Analysis.Complex.RealDeriv

namespace TwoAxisHelicoid
open Complex Set Filter Topology Metric
open scoped Topology ComplexConjugate ContDiff

/-- The local position in complex horizontal and real vertical
coordinates from the characteristic primitives A'=Φ₁+iΦ₂, B'=Φ₁−iΦ₂
and the height primitive C. -/
noncomputable def lopezRosPrimitivePosition (A B C : ℂ → ℂ) (k : ℝ) (z : ℂ) : ℂ × ℝ :=
  (((k:ℂ)*A z+conj (B z)/(k:ℂ))/2,(C z).re)

private noncomputable def rescaledPrimitivePosition
    (a b c : ℂ → ℂ) (ρ : ℂ) (d : ℝ) (q : ℝ × ℂ) : ℂ × ℝ :=
  let u := ρ*q.2
  let z := (q.1:ℂ)*u
  ((u^3*a z+conj (u*b z))/conj (ρ*b 0), (u^2*c z).re/d)

private theorem rescaledPrimitivePosition_limit {a b c : ℂ → ℂ} {ρ : ℂ} {d : ℝ}
    (hρ : ρ ≠ 0) (hb : b 0 ≠ 0) (hd : 0 < d)
    (hC : c 0*ρ^2 = (d:ℂ)) (hA : 3*a 0*ρ^3 = -conj (b 0*ρ)) (w : ℂ) :
    rescaledPrimitivePosition a b c ρ d (0,w) = enneperPosition w := by
  have n : conj (ρ*b 0) ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr (mul_ne_zero hρ hb)
  have eq : a 0*ρ^3 = -conj (ρ*b 0)/3 := by rw [mul_comm ρ]; linear_combination hA/3
  apply Prod.ext
  · change ((ρ*w)^3*a ((0:ℂ)*(ρ*w))+conj ((ρ*w)*b ((0:ℂ)*(ρ*w))))/conj (ρ*b 0) = _
    rw [zero_mul,show (ρ*w)^3*a 0 = (a 0*ρ^3)*w^3 by ring,eq,
      show (ρ*w)*b 0 = (ρ*b 0)*w by ring, map_mul (starRingEnd ℂ) (ρ*b 0) w]
    change _ = conj w-w^3/3
    apply (div_eq_iff n).mpr
    ring
  · change ((ρ*w)^2*c ((0:ℂ)*(ρ*w))).re/d = (w^2).re
    rw [zero_mul,show (ρ*w)^2*c 0 = w^2*(c 0*ρ^2) by ring,hC]
    simp [Complex.mul_re,hd.ne']

private theorem rescaledPrimitivePosition_regular {a b c : ℂ → ℂ}
    (ha : AnalyticAt ℂ a 0) (hb : AnalyticAt ℂ b 0) (hc : AnalyticAt ℂ c 0)
    (ρ : ℂ) (d : ℝ) (w : ℂ) : ContDiffAt ℝ 1 (rescaledPrimitivePosition a b c ρ d) (0,w) := by
  let Z := fun q : ℝ × ℂ => (q.1:ℂ)*(ρ*q.2)
  let V := fun q : ℝ × ℂ => ρ*q.2
  have hV : ContDiffAt ℝ 1 V (0,w) := contDiffAt_const.mul contDiffAt_snd
  have hZ : ContDiffAt ℝ 1 Z (0,w) := (Complex.ofRealCLM.contDiff.contDiffAt.comp _ contDiffAt_fst).mul hV
  have zero : Z (0,w) = 0 := by simp [Z]
  have localized (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) : ContDiffAt ℝ 1 (f ∘ Z) (0,w) := by
    have h := (hf.contDiffAt (n := 1)).restrict_scalars ℝ
    rw [← zero] at h
    exact h.comp _ hZ
  have h₁ := localized a ha
  have h₂ := localized b hb
  have h₃ := localized c hc
  have hhor := (((hV.pow 3).mul h₁).add (Complex.conjCLE.contDiff.contDiffAt.comp _
    (hV.mul h₂))).mul (contDiffAt_const (c := (conj (ρ*b 0))⁻¹))
  have hver := (Complex.reCLM.contDiff.contDiffAt.comp _ ((hV.pow 2).mul h₃)).mul (contDiffAt_const (c := d⁻¹))
  change ContDiffAt ℝ 1 (fun q => ((V q^3*(a ∘ Z) q + conj (V q*(b ∘ Z) q))/conj (ρ*b 0),
    (V q^2*(c ∘ Z) q).re/d)) (0,w)
  simp only [div_eq_mul_inv]
  exact hhor.prodMk hver

/-- The scaled local characteristic primitives have a genuine crossing
for every sufficiently large positive multiplier, in every chosen
neighborhood of the vertical point. The hypotheses are the local Taylor
factorizations of the original holomorphic primitives. -/
theorem lopez_ros_large_multiplier_of_factored_primitives (A B C a b c : ℂ → ℂ)
    (ha : AnalyticAt ℂ a 0) (hb : AnalyticAt ℂ b 0) (hc : AnalyticAt ℂ c 0)
    (hb₀ : b 0 ≠ 0) (hc₀ : c 0 ≠ 0) (hnull : 3*a 0*b 0+4*(c 0)^2 = 0)
    (hA : ∀ z, A z = A 0+z^3*a z) (hB : ∀ z, B z = B 0+z*b z)
    (hC : ∀ z, C z = C 0+z^2*c z) {U : Set ℂ} (hU : U ∈ 𝓝 0) :
    ∀ᶠ k : ℝ in atTop, ∃ x ∈ U, ∃ y ∈ U, x ≠ y ∧
      lopezRosPrimitivePosition A B C k x = lopezRosPrimitivePosition A B C k y := by
  obtain ⟨ρ,d,hρ,hd,hcr,har⟩ := lopez_ros_enneper_leading_coefficients hb₀ hc₀ hnull
  let F := rescaledPrimitivePosition a b c ρ d
  let r : ℂ := Real.sqrt 3
  let R : ℝ := ‖r‖+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hr : r ∈ ball (0:ℂ) R := by simp [R]
  have hneg : -r ∈ ball (0:ℂ) R := by simpa using hr
  have crosses := family_with_enneper_limit_has_double_points F
    (rescaledPrimitivePosition_limit hρ hb₀ hd hcr har)
    (rescaledPrimitivePosition_regular ha hb hc ρ d)
    (isOpen_ball.mem_nhds hr) (isOpen_ball.mem_nhds hneg)
  obtain ⟨e,he,heU⟩ := Metric.mem_nhds_iff.mp hU
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, ‖t‖*‖ρ‖*R < e := by
    have hc' : Continuous (fun t : ℝ => ‖t‖*‖ρ‖*R) := by fun_prop
    exact (hc'.continuousAt (x := 0)).eventually_lt_const (by simpa using he)
  have hlim : Tendsto (fun k : ℝ => k⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  filter_upwards [hlim.eventually crosses, hlim.eventually hsmall, eventually_gt_atTop (0:ℝ)] with k cross hs hk
  obtain ⟨u,hu,v,hv,huv,eq⟩ := cross
  let t : ℂ := ((k⁻¹:ℝ):ℂ)
  have ht : t ≠ 0 := Complex.ofReal_ne_zero.mpr (inv_ne_zero hk.ne')
  have inc (w : ℂ) (hw : w ∈ ball (0:ℂ) R) : t*(ρ*w) ∈ U := by
    apply heU
    rw [mem_ball_zero_iff,norm_mul,norm_mul,← mul_assoc]
    exact (mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hw).le (by positivity)).trans_lt (by simpa [t] using hs)
  refine ⟨t*(ρ*u),inc u hu,t*(ρ*v),inc v hv,fun h => huv (mul_left_cancel₀ hρ (mul_left_cancel₀ ht h)),?_⟩
  have eh := congrArg Prod.fst eq
  have ev := congrArg Prod.snd eq
  change ((ρ*u)^3*a (t*(ρ*u))+conj ((ρ*u)*b (t*(ρ*u))))/conj (ρ*b 0) =
    ((ρ*v)^3*a (t*(ρ*v))+conj ((ρ*v)*b (t*(ρ*v))))/conj (ρ*b 0) at eh
  have hh := (div_left_inj' ((map_ne_zero (starRingEnd ℂ)).mpr (mul_ne_zero hρ hb₀))).mp eh
  change ((ρ*u)^2*c (t*(ρ*u))).re/d = ((ρ*v)^2*c (t*(ρ*v))).re/d at ev
  have hvv := (div_left_inj' hd.ne').mp ev
  have hs₀ (w : ℂ) :
      lopezRosPrimitivePosition A B C k (t*(ρ*w)) =
        (((lopezRosPrimitivePosition A B C k 0).1 +
            t^2*((ρ*w)^3*a (t*(ρ*w))+conj ((ρ*w)*b (t*(ρ*w))))/2),
           (C 0).re + (k⁻¹)^2*((ρ*w)^2*c (t*(ρ*w))).re) := by
    apply Prod.ext
    · change ((k:ℂ)*A (t*(ρ*w))+conj (B (t*(ρ*w)))/(k:ℂ))/2 = _
      rw [hA (t*(ρ*w)), hB (t*(ρ*w))]
      have kt : (k:ℂ)*t = 1 := by simp [t,hk.ne']
      have real_t : conj t = t := Complex.conj_ofReal _
      have invk : (k:ℂ)⁻¹ = t := by simp [t]
      simp only [lopezRosPrimitivePosition,map_add,map_mul,real_t,div_eq_mul_inv,invk]
      linear_combination (t^2*(ρ*w)^3*a (t*(ρ*w))/2)*kt
    · change (C (t*(ρ*w))).re = _
      rw [hC (t*(ρ*w)),Complex.add_re,mul_pow]
      rw [mul_assoc]
      change (C 0).re + (((k⁻¹:ℝ):ℂ)^2*((ρ*w)^2*c (t*(ρ*w)))).re = _
      rw [← Complex.ofReal_pow]
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [hs₀ u,hs₀ v,hh,hvv]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.lopez_ros_large_multiplier_of_factored_primitives
