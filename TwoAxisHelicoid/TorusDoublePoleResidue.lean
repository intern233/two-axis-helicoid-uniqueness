import TwoAxisHelicoid.EllipticSimplePole
import TwoAxisHelicoid.EvenMeromorphicDoublePole

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- The unique double pole on a marked torus has zero residue. Subtracting
its leading Weierstrass term leaves at most one simple pole. -/
theorem torus_double_pole_has_zero_residue (L : PeriodPair) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (L.lattice : Set ℂ)ᶜ)
    (hp : ∀ z ω, ω ∈ L.lattice → f (z+ω) = f z)
    (hm : MeromorphicAt f 0) (ho : meromorphicOrderAt f 0 = (-2 : ℤ)) :
    ∃ (A : ℂ) (g : ℂ → ℂ), A ≠ 0 ∧ AnalyticAt ℂ g 0 ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → f z = A/z^2+g z := by
  obtain ⟨u,hu,hu0,hfac⟩ := (meromorphicOrderAt_eq_int_iff hm).mp ho
  let g := dslope (dslope u 0) 0
  let A := u 0
  let B := deriv u 0
  have hg : AnalyticAt ℂ g 0 := analyticAt_dslope_center (analyticAt_dslope_center hu)
  have ht : ∀ᶠ z in 𝓝[≠] (0 : ℂ), f z = A/z^2+B/z+g z := by
    filter_upwards [hfac,self_mem_nhdsWithin] with z hz hn
    have hn' : z ≠ 0 := hn
    have he : f z = u z / z^2 := by
      simpa [sub_zero,smul_eq_mul,zpow_neg,div_eq_mul_inv,mul_comm] using hz
    rw [he]
    have e1 := sub_smul_dslope u 0 z
    have e2 := sub_smul_dslope (dslope u 0) 0 z
    simp only [sub_zero,smul_eq_mul,dslope_same] at e1 e2
    dsimp only [A,B,g]
    field_simp [hn']
    linear_combination -e1-z*e2
  have ht' : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → f z = A/z^2+B/z+g z := by
    simpa only [eventually_nhdsWithin_iff,mem_compl_iff,mem_singleton_iff] using ht
  have hwp (z : ℂ) : L.weierstrassP z = 1/z^2+L.weierstrassPExcept 0 z := by
    simpa only [Submodule.coe_zero,sub_zero,zero_pow (by decide : 2 ≠ 0),div_zero,add_comm] using
      (L.weierstrassPExcept_add (0 : L.lattice) z).symm
  have hB := elliptic_single_simple_pole_coefficient_zero L (A := B)
    (f := fun z => f z-A*L.weierstrassP z)
    (g := fun z => g z-A*L.weierstrassPExcept 0 z)
    (fun z hz => (hf z hz).sub (analyticAt_const.mul (L.analyticOnNhd_weierstrassP z hz)))
    (fun z ω hω => by rw [hp z ω hω,L.weierstrassP_add_coe z (⟨ω,hω⟩ : L.lattice)])
    (hg.sub (analyticAt_const.mul (L.analyticAt_weierstrassPExcept 0))) (by
      filter_upwards [ht'] with z hz hn
      rw [hz hn,hwp]
      ring)
  refine ⟨A,g,hu0,hg,?_⟩
  simpa only [hB,zero_div,add_zero] using ht'

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.torus_double_pole_has_zero_residue
