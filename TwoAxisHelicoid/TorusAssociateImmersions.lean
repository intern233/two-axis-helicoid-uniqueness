import TwoAxisHelicoid.HarmonicTorusHeightFlux
import TwoAxisHelicoid.AssociatedPhase

namespace TwoAxisHelicoid
open Complex Set

/-- A spatial primitive on the same punctured torus of the three real
coordinate forms specified by complex coefficients. -/
def TorusCoordinatePrimitive (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (Φ : ℂ → Fin 3 → ℂ) : Prop :=
  ∀ z ∉ L.lattice, HasFDerivAt (puncturedTorusPullback L X) (nullRealDerivative (Φ z)) z

theorem TorusCoordinatePrimitive.component {L : PeriodPair} {X : PuncturedPeriodTorus L → Fin 3 → ℝ}
    {Φ : ℂ → Fin 3 → ℂ} (hX : TorusCoordinatePrimitive L X Φ) (j : Fin 3)
    {z : ℂ} (hz : z ∉ L.lattice) :
    HasFDerivAt (fun w => puncturedTorusPullback L X w j)
      (realCoefficientDerivative (Φ z j)) z :=
  (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp z (hX z hz)

theorem PlanePolygon.integral_const_mul {Ω : Set ℂ} {x y : ℂ} (p : PlanePolygon Ω x y)
    (c : ℂ) (f : ℂ → ℂ) : p.integral (fun z => c*f z) = c*p.integral f := by
  induction p with
  | refl => simp [PlanePolygon.integral]
  | step => simp only [PlanePolygon.integral,intervalIntegral.integral_const_mul]; ring
  | trans _ _ hp hq => simp only [PlanePolygon.integral,hp,hq,mul_add]

theorem torus_coordinate_phase_necessary (L : PeriodPair) {Φ : ℂ → Fin 3 → ℂ}
    (hf : AnalyticOnNhd ℂ (fun z => Φ z 2) (L.lattice : Set ℂ)ᶜ)
    (hp : ∀ z ω, ω ∈ L.lattice → Φ (z+ω) 2 = Φ z 2)
    (hm : MeromorphicAt (fun z => Φ z 2) 0) (ho : meromorphicOrderAt (fun z => Φ z 2) 0 = (-2 : ℤ))
    {X Y : PuncturedPeriodTorus L → Fin 3 → ℝ} (hX : TorusCoordinatePrimitive L X Φ)
    (θ : ℝ) (hY : TorusCoordinatePrimitive L Y (fun z j => exp ((θ:ℂ)*I)*Φ z j)) :
    ∃ k : ℤ, θ = (k:ℝ)*Real.pi := by
  let c := exp ((θ:ℂ)*I)
  have hreal (γ : TorusPeriodPolygon L) : (γ.edges.integral (fun z => Φ z 2)).re = 0 :=
    γ.height_period_re_zero hf (fun _ hz => hX.component 2 hz)
      (fun z ω hω => congrFun (puncturedTorusPullback_periodic L X z ω hω) 2)
  obtain ⟨x,y,p,hw,hn⟩ := torus_height_exists_nonzero_imaginary_period L hf hp hm ho
    (fun {x y} p hw => hreal ⟨x,y,p,hw⟩)
  apply (associated_periods_close_iff (fun γ : TorusPeriodPolygon L => γ.edges.integral (fun z => Φ z 2))
    hreal ⟨⟨x,y,p,hw⟩,hn⟩ θ).mp
  intro γ
  have hrot := γ.height_period_re_zero (f := fun z => c*Φ z 2)
    (fun z hz => analyticAt_const.mul (hf z hz)) (fun _ hz => hY.component 2 hz)
    (fun z ω hω => congrFun (puncturedTorusPullback_periodic L Y z ω hω) 2)
  rwa [γ.edges.integral_const_mul] at hrot

private theorem pullback_scale (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ) (a : ℝ) :
    puncturedTorusPullback L (fun q => a • X q) = fun z => a • puncturedTorusPullback L X z := by
  funext z
  by_cases hz : z ∉ L.lattice <;> simp [puncturedTorusPullback,hz]

theorem TorusCoordinatePrimitive.scale {L : PeriodPair} {Φ : ℂ → Fin 3 → ℂ}
    {X : PuncturedPeriodTorus L → Fin 3 → ℝ} (hX : TorusCoordinatePrimitive L X Φ) (a : ℝ) :
    TorusCoordinatePrimitive L (fun q => a • X q) (fun z j => (a:ℂ)*Φ z j) := by
  intro z hz
  rw [pullback_scale]
  have hd := (hX z hz).const_smul a
  rw [← nullRealDerivative_smul] at hd
  have he : a • Φ z = fun j => (a:ℂ)*Φ z j := by
    funext j
    simp only [Pi.smul_apply,Complex.real_smul]
  rw [he] at hd
  exact hd

theorem torus_associate_single_valued_iff (L : PeriodPair) {Φ : ℂ → Fin 3 → ℂ}
    (hf : AnalyticOnNhd ℂ (fun z => Φ z 2) (L.lattice : Set ℂ)ᶜ)
    (hp : ∀ z ω, ω ∈ L.lattice → Φ (z+ω) 2 = Φ z 2)
    (hm : MeromorphicAt (fun z => Φ z 2) 0) (ho : meromorphicOrderAt (fun z => Φ z 2) 0 = (-2 : ℤ))
    {X : PuncturedPeriodTorus L → Fin 3 → ℝ} (hX : TorusCoordinatePrimitive L X Φ) (θ : ℝ) :
    (∃ Y, TorusCoordinatePrimitive L Y (fun z j => exp ((θ:ℂ)*I)*Φ z j)) ↔
      ∃ k : ℤ, θ = (k:ℝ)*Real.pi := by
  constructor
  · rintro ⟨Y,hY⟩
    exact torus_coordinate_phase_necessary L hf hp hm ho hX θ hY
  · intro h
    rcases associated_phase_eq_sign h with he | he
    · exact ⟨X,by simpa only [he,one_mul] using hX⟩
    · refine ⟨fun q => (-1 : ℝ) • X q,?_⟩
      simpa only [he,ofReal_neg,ofReal_one] using hX.scale (-1)

theorem TorusCoordinatePrimitive.unique_up_to_translation {L : PeriodPair} {Φ : ℂ → Fin 3 → ℂ}
    {X Y : PuncturedPeriodTorus L → Fin 3 → ℝ} (hX : TorusCoordinatePrimitive L X Φ)
    (hY : TorusCoordinatePrimitive L Y Φ) :
    ∃ b : Fin 3 → ℝ, ∀ q, Y q = X q+b := by
  have hc : IsConnected (L.lattice : Set ℂ)ᶜ := Set.Countable.isConnected_compl_of_one_lt_rank
    (by simp) (countable_of_Lindelof_of_discrete (X := L.lattice))
  obtain ⟨b,hb⟩ := L.isClosed_lattice.isOpen_compl.exists_eq_add_of_fderiv_eq hc.isPreconnected
    (fun z hz => (hY z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hX z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => by rw [(hY z hz).fderiv,(hX z hz).fderiv])
  refine ⟨b,?_⟩
  intro q
  obtain ⟨⟨z,hz⟩,rfl⟩ := puncturedPlaneProjection_surjective L q
  simpa only [puncturedTorusPullback,dite_eq_left hz] using hb hz

/-- For a closed member of the associate family, its full spatial map on
the punctured quotient is either a translate or a central reflection and
translation, according to its phase. -/
theorem torus_associate_map_eq_sign_translation (L : PeriodPair) {Φ : ℂ → Fin 3 → ℂ}
    (hf : AnalyticOnNhd ℂ (fun z => Φ z 2) (L.lattice : Set ℂ)ᶜ)
    (hp : ∀ z ω, ω ∈ L.lattice → Φ (z+ω) 2 = Φ z 2)
    (hm : MeromorphicAt (fun z => Φ z 2) 0) (ho : meromorphicOrderAt (fun z => Φ z 2) 0 = (-2 : ℤ))
    {X Y : PuncturedPeriodTorus L → Fin 3 → ℝ} (hX : TorusCoordinatePrimitive L X Φ)
    (θ : ℝ) (hY : TorusCoordinatePrimitive L Y (fun z j => exp ((θ:ℂ)*I)*Φ z j)) :
    (exp ((θ:ℂ)*I) = 1 ∧ ∃ b, ∀ q, Y q = X q+b) ∨
    (exp ((θ:ℂ)*I) = -1 ∧ ∃ b, ∀ q, Y q = -X q+b) := by
  rcases associated_phase_eq_sign (torus_coordinate_phase_necessary L hf hp hm ho hX θ hY)
    with he | he
  · simp only [he,one_mul] at hY
    exact Or.inl ⟨he,hX.unique_up_to_translation hY⟩
  · have hd : TorusCoordinatePrimitive L (fun q => (-1:ℝ) • X q)
        (fun z j => exp ((θ:ℂ)*I)*Φ z j) := by
      simpa only [he,ofReal_neg,ofReal_one] using hX.scale (-1)
    exact Or.inr ⟨he,by simpa only [neg_one_smul] using hd.unique_up_to_translation hY⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.torus_associate_single_valued_iff
#print axioms TwoAxisHelicoid.torus_associate_map_eq_sign_translation
