import TwoAxisHelicoid.HeightFluxMonodromy
import TwoAxisHelicoid.TorusPathIntegrals
import TwoAxisHelicoid.LeftFluxDivergence

namespace TwoAxisHelicoid
open Complex Set MeasureTheory

/-- An arc integral of a holomorphic derivative equals the full complex
primitive difference, including the imaginary flux. -/
theorem ComplexPeriodArc.integral_eq_primitive_sub {Ω : Set ℂ} (p : ComplexPeriodArc Ω)
    {F f : ℂ → ℂ} (hf : ContinuousOn f Ω) (hF : ∀ z ∈ Ω, HasDerivAt F (f z) z) :
    p.integral f = F (p.curve p.right)-F (p.curve p.left) := by
  have hc := p.continuous_velocity.mul (hf.comp p.continuous_curve p.stays)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le p.ordered
    ((show ContinuousOn F Ω from fun _ hz => (hF _ hz).continuousAt.continuousWithinAt).comp
      p.continuous_curve p.stays) _ (hc.intervalIntegrable_of_Icc p.ordered)
  intro s hs
  exact (hF _ (p.stays ⟨hs.1.le,hs.2.le⟩)).scomp s (p.derivative s hs)

theorem actual_height_im_of_equal_projection {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 1)
    (hG : thetaG t a = 0) {z w : ℂ} (hz : z ∉ (rhombicPeriodPair t ht).lattice)
    (he : periodTorusProjection (rhombicPeriodPair t ht) z =
      periodTorusProjection (rhombicPeriodPair t ht) w) :
    ∃ k : ℤ, (actualComplexHeight t a c ht w).im-(actualComplexHeight t a c ht z).im =
      -(Real.pi*c/t)*(k:ℝ) := by
  have hω := (periodTorusProjection_eq_iff _ z w).mp he
  have h := actual_height_im_add_lattice (c := c) ht ha hG hz hω
  rw [show z+(w-z) = w by ring] at h
  obtain ⟨m,n,hmn⟩ := PeriodPair.mem_lattice.mp hω
  refine ⟨2*m+n,?_⟩
  rw [h]
  congr 1
  rw [← hmn]
  simp [rhombicPeriodPair,Complex.mul_re]
  ring

/-- The imaginary period along an actual quotient path differs from the
chosen endpoint representatives' conjugate-height difference by a lattice
flux. Lifts on adjacent arcs can start on different sheets. -/
theorem torus_height_integral_im_mod_period {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0:ℝ) 1) (hG : thetaG t a = 0)
    {q r : PuncturedPeriodTorus (rhombicPeriodPair t ht)} {γ : Path q r} {v : ℂ}
    (hv : TorusPathIntegral (rhombicPeriodPair t ht) (fun z => coordinateData t a c ht z 2) γ v)
    (x y : ℂ) (hx : periodTorusProjection (rhombicPeriodPair t ht) x = q.1)
    (hy : periodTorusProjection (rhombicPeriodPair t ht) y = r.1) :
    ∃ k : ℤ, v.im = (actualComplexHeight t a c ht y).im-(actualComplexHeight t a c ht x).im
      -(Real.pi*c/t)*(k:ℝ) := by
  let L := rhombicPeriodPair t ht
  let H := actualComplexHeight t a c ht
  have hn {q : PuncturedPeriodTorus L} {w : ℂ} (hw : periodTorusProjection L w = q.1) :
      w ∉ L.lattice := fun h => q.2 (hw.symm.trans ((periodTorusProjection_eq_zero L w).mpr h))
  induction hv generalizing x y with
  | refl q =>
    obtain ⟨k,hk⟩ := actual_height_im_of_equal_projection (c := c) ht ha hG (hn hx) (hx.trans hy.symm)
    refine ⟨-k,?_⟩
    rw [hk]
    simp
  | @arc q r γ p he =>
    have e₁ := he 0
    have e₂ := he 1
    simp only [γ.source,γ.target,ComplexPeriodArc.time,Set.Icc.coe_zero,Set.Icc.coe_one,
      AffineMap.lineMap_apply_zero,AffineMap.lineMap_apply_one] at e₁ e₂
    obtain ⟨k,hk⟩ := actual_height_im_of_equal_projection (c := c) ht ha hG (hn hx) (hx.trans e₁)
    obtain ⟨l,hl⟩ := actual_height_im_of_equal_projection (c := c) ht ha hG (hn hy) (hy.trans e₂)
    refine ⟨l-k,?_⟩
    rw [p.integral_eq_primitive_sub (F := H) _ (fun _ hz => actualComplexHeight_hasDerivAt ht hz),Complex.sub_im]
    · push_cast
      dsimp [H] at *
      linear_combination hl - hk
    · exact fun z hz => (((ContinuousLinearMap.proj 2 : (Fin 3 → ℂ) →L[ℂ] ℂ).analyticAt _).comp
        (coordinateData_analyticAt ht hz)).continuousAt.continuousWithinAt
  | @trans p q r γ δ v w _ _ ih₁ ih₂ =>
    obtain ⟨z,hz⟩ := (Quotient.mk_surjective : Function.Surjective (periodTorusProjection L)) q.1
    obtain ⟨k,hk⟩ := ih₁ x z hx hz
    obtain ⟨l,hl⟩ := ih₂ z y hz hy
    refine ⟨k+l,?_⟩
    rw [add_im,hk,hl,Int.cast_add]
    ring

/-- Arbitrary closed quotient paths with a defined piecewise smooth
integral have flux in the exact lattice computed from the generators. -/
theorem loop_height_flux_mem_generator_range {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 1)
    (hG : thetaG t a = 0) {q : PuncturedPeriodTorus (rhombicPeriodPair t ht)} {γ : Path q q} {v : ℂ}
    (hv : TorusPathIntegral (rhombicPeriodPair t ht) (fun z => coordinateData t a c ht z 2) γ v) :
    v.im ∈ range (heightBasisFlux t ht c) := by
  obtain ⟨x,hx⟩ := (Quotient.mk_surjective : Function.Surjective (periodTorusProjection _)) q.1
  obtain ⟨k,hk⟩ := torus_height_integral_im_mod_period ht ha hG hv x x hx hx
  rw [heightBasisFlux_range]
  refine ⟨-k,?_⟩
  change Real.pi*c/t*((-k:ℤ):ℝ) = v.im
  rw [hk,Int.cast_neg,sub_self]
  ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.loop_height_flux_mem_generator_range
