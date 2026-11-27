import TwoAxisHelicoid.IntrinsicLopezRosVariation
import TwoAxisHelicoid.PlanePolygonPrimitive

namespace TwoAxisHelicoid
open Complex Set InnerProductSpace

private def PiecewiseComplexPath.castEnds {Ω : Set ℂ} {x x' y y' : ℂ}
    (p : PiecewiseComplexPath Ω x y) (hx : x = x') (hy : y = y') : PiecewiseComplexPath Ω x' y' :=
  hx ▸ hy ▸ p

private theorem PiecewiseComplexPath.integral_castEnds {Ω : Set ℂ} {x x' y y' : ℂ}
    (p : PiecewiseComplexPath Ω x y) (hx : x = x') (hy : y = y') (f : ℂ → ℂ) :
    (p.castEnds hx hy).integral f = p.integral f := by subst x' y'; rfl

/-- The actual piecewise C¹ integral on a polygon agrees for every
coefficient with the polygon edge integral used to construct primitives. -/
theorem PlanePolygon.exists_piecewise_integral {Ω : Set ℂ} {x y : ℂ} (p : PlanePolygon Ω x y) :
    ∃ γ : PiecewiseComplexPath Ω x y, ∀ f : ℂ → ℂ, γ.integral f = p.integral f := by
  induction p with
  | refl z hz => exact ⟨.refl z hz,fun _ => rfl⟩
  | trans p q hp hq =>
    obtain ⟨γ,hγ⟩ := hp
    obtain ⟨δ,hδ⟩ := hq
    exact ⟨.trans γ δ,fun f => congrArg₂ (·+·) (hγ f) (hδ f)⟩
  | step x y hs =>
    let a : ComplexPeriodArc Ω := {
      left := 0
      right := 1
      ordered := zero_le_one
      curve := AffineMap.lineMap (k := ℝ) x y
      velocity := fun _ => y-x
      stays := fun s h => hs s h
      continuous_curve := AffineMap.lineMap_continuous.continuousOn
      continuous_velocity := continuousOn_const
      derivative := fun _ _ => AffineMap.hasDerivAt_lineMap }
    have h₀ : a.curve a.left = x := AffineMap.lineMap_apply_zero _ _
    have h₁ : a.curve a.right = y := AffineMap.lineMap_apply_one _ _
    refine ⟨(PiecewiseComplexPath.arc a).castEnds h₀ h₁,fun f => ?_⟩
    rw [PiecewiseComplexPath.integral_castEnds]
    change (∫ s : ℝ in 0..1, (y-x)*f (AffineMap.lineMap (k := ℝ) x y s)) =
      (y-x)*∫ s : ℝ in 0..1, f (AffineMap.lineMap (k := ℝ) x y s)
    rw [intervalIntegral.integral_const_mul]

/-- Everywhere vertical flux on an actual single-valued harmonic torus
immersion makes both horizontal coordinate forms complex-exact on the
punctured torus. Their primitives are periodic, including deck paths
which are open in the covering plane. -/
theorem vertical_flux_horizontal_primitives (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (hX : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L X w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L X) z)
    (hflux : ¬ HasIntrinsicNonverticalFlux L X) :
    ∃ F : Fin 2 → ℂ → ℂ, (∀ j z ω, ω ∈ L.lattice → F j (z+ω) = F j z) ∧
      ∀ j z, z ∉ L.lattice → HasDerivAt (F j) (torusImmersionForms L X z j.castSucc) z := by
  classical
  let p := torusImmersionForms L X
  obtain ⟨ha,_,hd⟩ := torusImmersionForms_regular L X (fun z hz => (hX z hz).1) (fun z hz => (hX z hz).2)
  have hn : ¬ HasNonverticalTorusFlux L X := fun h => hflux ((nonvertical_flux_iff_intrinsic L X).mp h)
  have aux (j : Fin 2) : ∃ F : ℂ → ℂ, (∀ z ω, ω ∈ L.lattice → F (z+ω) = F z) ∧
      ∀ z ∉ L.lattice, HasDerivAt F (p z j.castSucc) z := by
    apply periodic_primitive_of_zero_polygon_periods L (fun z hz => ha z hz j.castSucc)
    intro x y δ hxy
    obtain ⟨γ,hγ⟩ := δ.exists_piecewise_integral
    have eq := (periodTorusProjection_eq_iff L x y).mpr hxy
    have hRe := γ.integral_re_eq_sub (f := fun z => p z j.castSucc)
      (X := fun z => torusFilledPosition L X (periodTorusProjection L z) j.castSucc)
      (fun z hz => (ha z hz j.castSucc).continuousAt.continuousWithinAt)
      (fun z hz => (ContinuousLinearMap.proj j.castSucc : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp z (hd z hz))
    rw [eq,sub_self] at hRe
    rw [← hγ]
    refine Complex.ext hRe ?_
    by_contra hIm
    apply hn
    refine ⟨x,y,γ,eq,?_⟩
    fin_cases j
    · exact Or.inl hIm
    · exact Or.inr hIm
  choose F hp hD using aux
  exact ⟨F,hp,hD⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.vertical_flux_horizontal_primitives
