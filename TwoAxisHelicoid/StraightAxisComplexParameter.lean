import TwoAxisHelicoid.HarmonicAxisReflection
import Mathlib.Analysis.Complex.HasPrimitives

namespace TwoAxisHelicoid
open Complex Set Metric Filter
open scoped Topology

theorem horizontal_null_velocity {v : ℂ} {p : Fin 3 → ℂ} (hp : ComplexNull p)
    (h : nullRealDerivative p v = ![1,0,0]) : v*p 0 = 1 := by
  let q := fun j => v*p j
  have hq : ComplexNull q := by
    unfold ComplexNull at hp ⊢
    dsimp [q]
    linear_combination v^2*hp
  have he := (complexNull_real_identities hq).2
  have h0 : (q 0).re = 1 := congrFun h 0
  have h1 : (q 1).re = 0 := congrFun h 1
  have h2 : (q 2).re = 0 := congrFun h 2
  rw [h0,h1,h2] at he
  exact Complex.ext h0 (by change (q 0).im = 0; simpa only [one_mul,zero_mul,add_zero] using he)

/-- On a straight line of a null immersion, its horizontal holomorphic
coordinate has unit complex velocity along the actual parameter curve. -/
theorem horizontal_coordinate_unit_velocity {X : ℂ → Fin 3 → ℝ} {σ v : ℝ → ℂ} {p : Fin 3 → ℂ}
    {s : ℝ} (hσ : HasDerivAt σ (v s) s) (hp : ComplexNull p)
    (hX : HasFDerivAt X (nullRealDerivative p) (σ s))
    (he : ∀ᶠ t in 𝓝 s, X (σ t) = ![t,0,0]) : v s*p 0 = 1 := by
  have hd := hX.comp_hasDerivAt s hσ
  have hline : HasDerivAt (fun t : ℝ => (![t,0,0] : Fin 3 → ℝ)) ![1,0,0] s := by
    apply hasDerivAt_pi.mpr
    intro j
    fin_cases j
    · exact hasDerivAt_id s
    · exact hasDerivAt_const s 0
    · exact hasDerivAt_const s 0
  have heq : (fun t => (![t,0,0] : Fin 3 → ℝ)) =ᶠ[𝓝 s] X ∘ σ := EventuallyEq.symm he
  exact horizontal_null_velocity hp ((hd.congr_of_eventuallyEq heq).unique hline)

/-- A harmonic conjugate of the first actual spatial coordinate straightens
the full parameter segment on the surface's horizontal line. -/
theorem straight_axis_exists_holomorphic_coordinate {X : ℂ → Fin 3 → ℝ} {Φ : ℂ → Fin 3 → ℂ}
    {σ v : ℝ → ℂ} {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hΦ : AnalyticOnNhd ℂ (fun z => Φ z 0) (ball (σ 0) R))
    (hp : ∀ z ∈ ball (σ 0) R, ComplexNull (Φ z))
    (hX : ∀ z ∈ ball (σ 0) R, HasFDerivAt X (nullRealDerivative (Φ z)) z)
    (hσ : ∀ s ∈ Ioo (-r) r, HasDerivAt σ (v s) s)
    (hb : MapsTo σ (Ioo (-r) r) (ball (σ 0) R))
    (ha : ∀ s ∈ Ioo (-r) r, X (σ s) = ![s,0,0]) :
    ∃ W : ℂ → ℂ, (∀ z ∈ ball (σ 0) R, HasDerivAt W (Φ z 0) z) ∧
      (∀ s ∈ Ioo (-r) r, W (σ s) = (s:ℂ)) ∧ deriv W (σ 0) ≠ 0 ∧
      ∀ z ∈ ball (σ 0) R, (W z).re = X z 0 := by
  have hd : DifferentiableOn ℂ (fun z => Φ z 0) (ball (σ 0) R) :=
    fun z hz => (hΦ z hz).differentiableAt.differentiableWithinAt
  obtain ⟨W,hW0,hW⟩ := hd.isExactOn_ball.with_val_at (σ 0) 0
  have h0 : (0:ℝ) ∈ Ioo (-r) r := ⟨neg_lt_zero.mpr hr,hr⟩
  have hvel (s : ℝ) (hs : s ∈ Ioo (-r) r) : v s*Φ (σ s) 0 = 1 := by
    apply horizontal_coordinate_unit_velocity (hσ s hs) (hp _ (hb hs)) (hX _ (hb hs))
    filter_upwards [isOpen_Ioo.mem_nhds hs] with w hw
    exact ha w hw
  have hder (s : ℝ) (hs : s ∈ Ioo (-r) r) : HasDerivAt (fun t => W (σ t)) (1:ℂ) s := by
    simpa only [Function.comp_def,smul_eq_mul,hvel s hs] using! (hW _ (hb hs)).scomp s (hσ s hs)
  have hsub (s : ℝ) (hs : s ∈ Ioo (-r) r) :
      HasDerivAt (fun t : ℝ => W (σ t)-(t:ℂ)) 0 s := by
    have he : HasDerivAt (fun t : ℝ => (t:ℂ)) (1:ℂ) s := Complex.ofRealCLM.hasDerivAt
    simpa only [sub_self] using! (hder s hs).sub he
  obtain ⟨C,hC⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun s hs => (hsub s hs).differentiableAt.differentiableWithinAt) (fun s hs => (hsub s hs).deriv)
  have hC0 : C = 0 := by simpa [hW0] using (hC 0 h0).symm
  have hne : Φ (σ 0) 0 ≠ 0 := by
    intro he
    have := hvel 0 h0
    simp [he] at this
  refine ⟨W,hW,fun s hs => sub_eq_zero.mp ((hC s hs).trans hC0),?_,?_⟩
  · simpa only [(hW _ (mem_ball_self hR)).deriv] using hne
  · have hXr (z : ℂ) (hz : z ∈ ball (σ 0) R) : HasFDerivAt (fun w => X w 0)
        (realCoefficientDerivative (Φ z 0)) z :=
      (ContinuousLinearMap.proj 0 : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp z (hX z hz)
    have hWr (z : ℂ) (hz : z ∈ ball (σ 0) R) : HasFDerivAt (fun w => (W w).re)
        (realCoefficientDerivative (Φ z 0)) z :=
      Complex.reCLM.hasFDerivAt.comp z ((hW z hz).hasFDerivAt.restrictScalars ℝ)
    obtain ⟨c,he⟩ := isOpen_ball.exists_eq_add_of_fderiv_eq (convex_ball (σ 0) R).isPreconnected
      (fun z hz => (hWr z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hXr z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => by rw [(hWr z hz).fderiv,(hXr z hz).fderiv])
    have hbase := he (mem_ball_self hR)
    change (W (σ 0)).re = X (σ 0) 0 + c at hbase
    rw [hW0,ha _ h0] at hbase
    have hcz : c = 0 := by simpa using hbase.symm
    exact fun z hz => by simpa only [hcz,add_zero] using he hz

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.straight_axis_exists_holomorphic_coordinate
