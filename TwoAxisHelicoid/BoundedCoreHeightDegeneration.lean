import TwoAxisHelicoid.TorusHeightFluxMonodromy
import TwoAxisHelicoid.HorizontalTangentFluxLength

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology Manifold ENNReal

/-- The conjugate-height period of a coherent lifted path uses its
actual deck displacement. -/
theorem piecewise_height_integral_im_deck {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 1)
    (hG : thetaG t a = 0) {x y : ℂ} (hx : x ∉ (rhombicPeriodPair t ht).lattice)
    (γ : PiecewiseComplexPath ((rhombicPeriodPair t ht).lattice : Set ℂ)ᶜ x y)
    (hxy : y-x ∈ (rhombicPeriodPair t ht).lattice) :
    (γ.integral (fun z => coordinateData t a c ht z 2)).im = -(Real.pi*c/t)*(y-x).re := by
  let H := actualComplexHeight t a c ht
  have he {u v : ℂ} (δ : PiecewiseComplexPath ((rhombicPeriodPair t ht).lattice : Set ℂ)ᶜ u v) :
      δ.integral (fun z => coordinateData t a c ht z 2) = H v-H u := by
    induction δ with
    | refl => simp [PiecewiseComplexPath.integral]
    | arc b =>
      apply b.integral_eq_primitive_sub _ (fun _ hz => actualComplexHeight_hasDerivAt ht hz)
      exact fun z hz => (((ContinuousLinearMap.proj 2 : (Fin 3 → ℂ) →L[ℂ] ℂ).analyticAt _).comp
        (coordinateData_analyticAt ht hz)).continuousAt.continuousWithinAt
    | trans p q hp hq => change p.integral _+q.integral _ = _; rw [hp,hq]; ring
  have h := actual_height_im_add_lattice (c := c) ht ha hG hx hxy
  rw [show x+(y-x) = y by ring] at h
  simpa only [he γ,Complex.sub_im] using h

/-- Two generating deck displacements cannot both have zero real parts
in a nondegenerate marked lattice. -/
theorem generating_deck_displacements_nonvertical (L : PeriodPair) {v w : ℂ}
    (hb : ∀ ω ∈ L.lattice, ∃ m n : ℤ, ω = (m:ℂ)*v+(n:ℂ)*w) :
    v.re ≠ 0 ∨ w.re ≠ 0 := by
  by_contra! h
  have he : ∀ z ∈ L.lattice, z.re = 0 := by
    intro z hz
    obtain ⟨m,n,rfl⟩ := hb z hz
    simp [Complex.mul_re,h.1,h.2]
  have hker : Submodule.span ℝ (L.lattice : Set ℂ) ≤ LinearMap.ker Complex.reCLM.toLinearMap :=
    Submodule.span_le.mpr (fun z hz => he z hz)
  rw [IsZLattice.span_top] at hker
  have h₁ : (1:ℂ).re = 0 := hker (show (1:ℂ) ∈ (⊤ : Submodule ℝ ℂ) from trivial)
  simp at h₁

/-- The compact-core contradiction excludes a sequence with two bounded
generating curves after fixing the pitch. It uses only height-flux growth;
there is no horizontal period sign input. -/
theorem normalized_height_nonzero_flux_precludes_bounded_sequence
    {t : ℕ → ℝ} (hlim : Tendsto t atTop (𝓝[>] 0))
    (ht : ∀ n, 0 < t n) {c : ℕ → ℝ} (hc : ∀ n, |c n| = 2*(1-verticalA (t n)))
    (B : ℝ) {v : ℕ → ℝ} (hb : ∀ n, |v n| ≤ B) (hn : ∀ n, v n ≠ 0)
    (hv : ∀ n, v n ∈ range (heightBasisFlux (t n) (ht n) (c n))) : False := by
  have he := hlim.eventually (normalized_height_basis_flux_eventually_large (B+1))
  obtain ⟨n,hh⟩ := he.exists
  have hs := hh (ht n) (c n) (v n) (hc n) (hv n) (hn n)
  linarith [hb n]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.piecewise_height_integral_im_deck
#print axioms TwoAxisHelicoid.normalized_height_nonzero_flux_precludes_bounded_sequence
