import TwoAxisHelicoid.EllipticPrincipalPart

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- Every finite complex value is attained by the genuine Weierstrass
function away from its period lattice. -/
theorem weierstrassP_attains_every_finite_value (L : PeriodPair) (u : ℂ) :
    ∃ z ∉ L.lattice, L.weierstrassP z = u := by
  by_contra! hn
  let f : ℂ → ℂ := fun z => (L.weierstrassP z-u)⁻¹
  let g : ℂ → ℂ := fun z => z^2/(1+z^2*(L.weierstrassPExcept 0 z-u))
  have hg : AnalyticAt ℂ g 0 := by
    apply (analyticAt_id.pow 2).div
      (analyticAt_const.add ((analyticAt_id.pow 2).mul
        ((L.analyticAt_weierstrassPExcept 0).sub analyticAt_const)))
    simp
  have hloc : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → f z = g z := by
    apply Eventually.of_forall
    intro z hz
    have hwp : L.weierstrassP z = L.weierstrassPExcept 0 z+1/z^2 := by
      simpa using (L.weierstrassPExcept_add (0 : L.lattice) z).symm
    have he : 1+z^2*(L.weierstrassPExcept 0 z-u) = z^2*(L.weierstrassP z-u) := by
      rw [hwp]
      field_simp
      ring
    dsimp only [f,g]
    rw [he,div_mul_eq_div_div,div_self (pow_ne_zero 2 hz),one_div]
  have he := elliptic_removable_puncture_constant L
    (f := f) (g := g)
    (fun z hz => ((L.analyticOnNhd_weierstrassP z hz).differentiableAt.sub_const u).inv
      (sub_ne_zero.mpr (hn z hz)))
    (fun z ω hω => by dsimp only [f]; rw [L.weierstrassP_add_coe z (⟨ω,hω⟩ : L.lattice)]) hg hloc
  have h := he (L.ω₁/2) L.ω₁_div_two_notMem_lattice
  have hfne : f (L.ω₁/2) ≠ 0 := inv_ne_zero (sub_ne_zero.mpr (hn _ L.ω₁_div_two_notMem_lattice))
  apply hfne
  simpa [g] using h

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.weierstrassP_attains_every_finite_value
