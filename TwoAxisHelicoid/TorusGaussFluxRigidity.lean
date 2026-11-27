import TwoAxisHelicoid.GaussMultiplierContinuation
import TwoAxisHelicoid.HorizontalFluxMultiplier
import TwoAxisHelicoid.WeierstrassRotation
import TwoAxisHelicoid.PuncturedLatticePlane
import TwoAxisHelicoid.PlanePolygonPrimitive

namespace TwoAxisHelicoid
open Complex Set Metric Filter
open scoped Topology ComplexConjugate

theorem null_derivative_rotates_from_horizontal_forms {u v : Fin 3 → ℂ} {c : ℂ} (hc : ‖c‖ = 1)
    (hp : nullHorizontalPlus v = c*nullHorizontalPlus u)
    (hm : nullHorizontalMinus v = c⁻¹*nullHorizontalMinus u) (hh : v 2 = u 2) :
    nullRealDerivative v = (verticalRotation c).comp (nullRealDerivative u) := by
  rw [Complex.inv_eq_conj hc] at hm
  have hr := (Complex.re_add_im c).symm
  unfold nullHorizontalPlus at hp
  unfold nullHorizontalMinus at hm
  conv_rhs at hp => rw [hr]
  conv_rhs at hm => rw [hr]
  simp only [map_add,map_mul,Complex.conj_ofReal,Complex.conj_I] at hm
  have h₀ : v 0 = (c.re:ℂ)*u 0-(c.im:ℂ)*u 1 := by
    linear_combination (hp+hm)/2 + (c.im:ℂ)*u 1 * I_sq
  have h₁ : v 1 = (c.im:ℂ)*u 0+(c.re:ℂ)*u 1 := by
    linear_combination -I*(hp-hm)/2 + (v 1-(c.re:ℂ)*u 1-(c.im:ℂ)*u 0)*I_sq
  ext w j
  fin_cases j <;> simp [h₀,h₁,hh,verticalRotation_apply,Complex.mul_re,Complex.mul_im] <;> ring

/-- The actual coefficients of two single-valued immersions on an arbitrary
marked torus with fixed height and Gauss logarithmic derivative determine
one vertical rotation and translation. The horizontal flux witness is any
closed piecewise smooth lifted path of the first immersion. -/
theorem punctured_torus_fixed_gauss_log_rigid_motion (L : PeriodPair)
    (X Y : PeriodTorus L → Fin 3 → ℝ) (p q : ℂ → Fin 3 → ℂ)
    (hp : ∀ z ∉ L.lattice, ∀ j, AnalyticAt ℂ (fun w => p w j) z)
    (hq : ∀ z ∉ L.lattice, ∀ j, AnalyticAt ℂ (fun w => q w j) z)
    (hpn : ∀ z ∉ L.lattice, ComplexNull (p z)) (hqn : ∀ z ∉ L.lattice, ComplexNull (q z))
    (hX : ∀ z ∉ L.lattice, HasFDerivAt (X ∘ periodTorusProjection L) (nullRealDerivative (p z)) z)
    (hY : ∀ z ∉ L.lattice, HasFDerivAt (Y ∘ periodTorusProjection L) (nullRealDerivative (q z)) z)
    (hh : ∀ z ∉ L.lattice, q z 2 = p z 2)
    (hl : ∀ z ∉ L.lattice, p z 2 ≠ 0 → deriv (nullGauss ∘ q) z/nullGauss (q z)
      = deriv (nullGauss ∘ p) z/nullGauss (p z))
    {w : ℂ} (hw : w ∉ L.lattice) (hw' : p w 2 ≠ 0)
    {x y : ℂ} (γ : PiecewiseComplexPath (L.lattice : Set ℂ)ᶜ x y)
    (hγ : periodTorusProjection L x = periodTorusProjection L y)
    (hflux : (γ.integral (fun z => p z 0)).im ≠ 0 ∨ (γ.integral (fun z => p z 1)).im ≠ 0) :
    ∃ θ : ℝ, ∃ b : Fin 3 → ℝ, ∀ s : PuncturedPeriodTorus L,
        Y s.1 = verticalRotation (exp ((θ:ℂ)*I)) (X s.1)+b := by
  let U := (L.lattice : Set ℂ)ᶜ
  have hopen : IsOpen U := L.isClosed_lattice.isOpen_compl
  have hcount : (L.lattice : Set ℂ).Countable := countable_of_Lindelof_of_discrete (X := L.lattice)
  have hu : IsPreconnected U := (hcount.isConnected_compl_of_one_lt_rank
    (by rw [← Module.finrank_eq_rank,Complex.finrank_real_complex]; norm_num : 1 < Module.rank ℝ ℂ)).isPreconnected
  obtain ⟨c,hc,he⟩ := horizontal_forms_of_equal_gauss_log hopen hu hp hq hpn hqn hh hw hw' hl
  have zero {V : PeriodTorus L → Fin 3 → ℝ} {u : ℂ → Fin 3 → ℂ}
      (hv : ∀ z ∈ U, HasFDerivAt (V ∘ periodTorusProjection L) (nullRealDerivative (u z)) z)
      (ha : ∀ z ∈ U, ∀ j, AnalyticAt ℂ (fun w => u w j) z) (j : Fin 3) :
      (γ.integral (fun z => u z j)).re = 0 := by
    have e := γ.integral_re_eq_sub (fun z hz => (ha z hz j).continuousAt.continuousWithinAt)
      (X := fun z => V (periodTorusProjection L z) j)
      (fun z hz => (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp z (hv z hz))
    simpa [hγ] using e
  have hc' := unit_multiplier_of_horizontal_flux γ (fun j z hz => (hp z hz j).continuousAt.continuousWithinAt)
    (fun j z hz => (hq z hz j).continuousAt.continuousWithinAt) hc he (zero hX hp) (zero hY hq) hflux
  have hr z hz := (verticalRotation c).hasFDerivAt.comp z (hX z hz)
  obtain ⟨b,hb⟩ := hopen.exists_eq_add_of_fderiv_eq hu
    (fun z hz => (hY z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hr z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => by rw [(hY z hz).fderiv,(hr z hz).fderiv,
      null_derivative_rotates_from_horizontal_forms hc' (he z hz).1 (he z hz).2 (hh z hz)])
  have hphase := Complex.norm_mul_exp_arg_mul_I c
  rw [hc',Complex.ofReal_one,one_mul] at hphase
  refine ⟨arg c,b,?_⟩
  rw [hphase]
  intro s
  obtain ⟨z,hz⟩ := (Quotient.mk_surjective : Function.Surjective (periodTorusProjection L)) s.1
  have hn : z ∉ L.lattice := fun h => s.2 (hz.symm.trans ((periodTorusProjection_eq_zero L z).mpr h))
  rw [← hz]
  exact hb hn

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.punctured_torus_fixed_gauss_log_rigid_motion
