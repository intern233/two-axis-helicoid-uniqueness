import TwoAxisHelicoid.ActualHorizontalPhaseRigidity
import TwoAxisHelicoid.WeierstrassRotation
import TwoAxisHelicoid.HeightPathPeriods

namespace TwoAxisHelicoid
open Complex Set Metric
set_option maxHeartbeats 1000000

namespace HolomorphicCoefficientDisks
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

theorem scalar_segment_real_integral {A : HolomorphicCoefficientDisks M} {U : Set M}
    {H : M → ℝ} {F : M → ℂ → ℂ}
    (hF : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) → (chartAt ℂ p).symm z ∈ U →
      ContinuousAt (F p) z)
    (hH : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) → (chartAt ℂ p).symm z ∈ U →
      HasFDerivAt (fun w : ℂ => H ((chartAt ℂ p).symm w)) (realCoefficientDerivative (F p z)) z)
    (p : M) {x y : M} (hx : x ∈ A.primitives.domain p) (hy : y ∈ A.primitives.domain p)
    (hU : ∀ s : ℝ, s ∈ Icc 0 1 → (chartAt ℂ p).symm (chartSegment p x y s) ∈ U) :
    (∫ s : ℝ in 0..1, (chartAt ℂ p y-chartAt ℂ p x)*F p (chartSegment p x y s)).re = H y-H x := by
  have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s => H ((chartAt ℂ p).symm (chartSegment p x y s)))
        (((chartAt ℂ p y-chartAt ℂ p x)*F p (chartSegment p x y s)).re) s := by
    have he := (hH p _ (A.chartSegment_mem p hx hy hs) (hU s hs)).comp_hasDerivAt s
      (AffineMap.hasDerivAt_lineMap (𝕜 := ℝ)
        (a := chartAt ℂ p x) (b := chartAt ℂ p y) (x := s))
    simpa only [Function.comp_def,realCoefficientDerivative_apply] using! he
  have hi := segment_coefficient_integrable hF p hx hy hU
  have hri := And.intro (Complex.reCLM.integrable_comp hi.1) (Complex.reCLM.integrable_comp hi.2)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hd s (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs)) hri
  have hInt := Complex.reCLM.intervalIntegral_comp_comm hi
  change (∫ s : ℝ in 0..1, ((chartAt ℂ p y-chartAt ℂ p x)*F p (chartSegment p x y s)).re) =
    (∫ s : ℝ in 0..1, (chartAt ℂ p y-chartAt ℂ p x)*F p (chartSegment p x y s)).re at hInt
  rw [hInt] at he
  simpa only [chartSegment,AffineMap.lineMap_apply_one,AffineMap.lineMap_apply_zero,
    (chartAt ℂ p).left_inv hx.1,(chartAt ℂ p).left_inv hy.1] using! he

theorem AvoidingPath.scalar_real_integral {A : HolomorphicCoefficientDisks M} {U : Set M}
    {H : M → ℝ} {F : M → ℂ → ℂ}
    (hF : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) → (chartAt ℂ p).symm z ∈ U →
      ContinuousAt (F p) z)
    (hH : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) → (chartAt ℂ p).symm z ∈ U →
      HasFDerivAt (fun w : ℂ => H ((chartAt ℂ p).symm w)) (realCoefficientDerivative (F p z)) z)
    {x y : M} (c : A.AvoidingPath U x y) : (c.integral F).re = H y-H x := by
  induction c with
  | refl => simp only [integral,zero_re,sub_self]
  | step p x y hx hy hU => exact scalar_segment_real_integral hF hH p hx hy hU
  | trans c d hc hd => simp only [integral,add_re,hc,hd]; ring

theorem AvoidingPath.integral_add {A : HolomorphicCoefficientDisks M} {U : Set M}
    {x y : M} (c : A.AvoidingPath U x y) {F G : M → ℂ → ℂ}
    (hF : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) → (chartAt ℂ p).symm z ∈ U →
      ContinuousAt (F p) z)
    (hG : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) → (chartAt ℂ p).symm z ∈ U →
      ContinuousAt (G p) z) : c.integral (fun p z => F p z+G p z) = c.integral F+c.integral G := by
  induction c with
  | refl => simp only [integral,add_zero]
  | step p x y hx hy hU =>
      simp only [integral,mul_add]
      exact intervalIntegral.integral_add
        (segment_coefficient_integrable hF p hx hy hU)
        (segment_coefficient_integrable hG p hx hy hU)
  | trans c d hc hd => simp only [integral,hc,hd]; ring

/-- A single-valued actual coordinate map forces both horizontal real
periods to close. The hypotheses are local differential equations and
continuity, not precomputed period identities. -/
theorem actual_weierstrass_horizontal_periods_close
    {A : HolomorphicCoefficientDisks M} {U : Set M} {X : M → Fin 3 → ℝ}
    {g : M → ℂ} {dh : M → ℂ → ℂ}
    (hg : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) → (chartAt ℂ p).symm z ∈ U →
      ContinuousAt (fun w : ℂ => g ((chartAt ℂ p).symm w)) z)
    (hn : ∀ x ∈ U, g x ≠ 0)
    (hh : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) → (chartAt ℂ p).symm z ∈ U →
      ContinuousAt (dh p) z)
    (hX : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) → (chartAt ℂ p).symm z ∈ U →
      HasFDerivAt (fun w : ℂ => X ((chartAt ℂ p).symm w))
        (nullRealDerivative (weierstrassTriple (g ((chartAt ℂ p).symm z)) (dh p z))) z)
    {x : M} (c : A.AvoidingPath U x x) : HorizontalLinePeriodsClose c g dh := by
  let F := weightedGaussCoefficient g dh
  let G := inverseGaussCoefficient g dh
  have hF p z hz hu : ContinuousAt (F p) z := (hg p z hz hu).mul (hh p z hz hu)
  have hG p z hz hu : ContinuousAt (G p) z := ((hg p z hz hu).inv₀ (hn _ hu)).mul (hh p z hz hu)
  have hφ (j : Fin 3) (p : M) (z : ℂ)
      (hz : z ∈ ball (chartAt ℂ p p) (A.radius p)) (hu : (chartAt ℂ p).symm z ∈ U) :
      ContinuousAt (fun z => weierstrassTriple (g ((chartAt ℂ p).symm z)) (dh p z) j) z := by
    fin_cases j
    · exact (((hg p z hz hu).inv₀ (hn _ hu)).sub (hg p z hz hu)).div_const 2 |>.mul (hh p z hz hu)
    · exact (continuousAt_const.mul (((hg p z hz hu).inv₀ (hn _ hu)).add (hg p z hz hu))).div_const 2 |>.mul (hh p z hz hu)
    · exact hh p z hz hu
  have hcoord (j : Fin 3) (p : M) (z : ℂ)
      (hz : z ∈ ball (chartAt ℂ p p) (A.radius p)) (hu : (chartAt ℂ p).symm z ∈ U) :
      HasFDerivAt (fun w : ℂ => X ((chartAt ℂ p).symm w) j)
        (realCoefficientDerivative (weierstrassTriple (g ((chartAt ℂ p).symm z)) (dh p z) j)) z := by
    exact (ContinuousLinearMap.proj j).hasFDerivAt.comp z (hX p z hz hu)
  have hzero (j : Fin 3) := c.scalar_real_integral (H := fun x => X x j) (hφ j) (hcoord j)
  have h₀ : c.integral (fun p z => weierstrassTriple (g ((chartAt ℂ p).symm z)) (dh p z) 0) =
      (c.integral G-c.integral F)/2 := by
    calc
      _ = c.integral (fun p z => (1/2 : ℂ)*(G p z-F p z)) := by
        apply c.integral_congr
        intro p z _hz _hu
        dsimp [weierstrassTriple,F,G,weightedGaussCoefficient,inverseGaussCoefficient]
        ring
      _ = _ := by rw [c.integral_const_mul,c.integral_sub hG hF]; ring
  have h₁ : c.integral (fun p z => weierstrassTriple (g ((chartAt ℂ p).symm z)) (dh p z) 1) =
      I*(c.integral G+c.integral F)/2 := by
    calc
      _ = c.integral (fun p z => (I/2)*(G p z+F p z)) := by
        apply c.integral_congr
        intro p z _hz _hu
        dsimp [weierstrassTriple,F,G,weightedGaussCoefficient,inverseGaussCoefficient]
        ring
      _ = _ := by rw [c.integral_const_mul,c.integral_add hG hF]; ring
  constructor
  · rw [← h₀,hzero 0,sub_self]
  · rw [← h₁,hzero 1,sub_self]

end HolomorphicCoefficientDisks
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.HolomorphicCoefficientDisks.actual_weierstrass_horizontal_periods_close
