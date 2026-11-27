import TwoAxisHelicoid.NullGaussDivisor

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

theorem flipNullY_analyticAt {p : ℂ → Fin 3 → ℂ} {z : ℂ}
    (hp : ∀ j, AnalyticAt ℂ (fun w => p w j) z) :
    ∀ j, AnalyticAt ℂ (fun w => flipNullY (p w) j) z := by
  intro j
  fin_cases j
  · exact hp 0
  · exact (hp 1).neg
  · exact hp 2

theorem flipNullY_gauss_inverse {p : Fin 3 → ℂ} (hp : ComplexNull p) :
    nullGauss (flipNullY p) = -(nullGauss p)⁻¹ := by
  by_cases hplus : nullHorizontalPlus p = 0
  · have he := null_horizontal_product hp
    rw [hplus,mul_zero,eq_comm,neg_eq_zero] at he
    have h2 : p 2 = 0 := by
      have hsq : p 2*p 2 = 0 := by simpa only [pow_two] using he
      exact (mul_eq_zero.mp hsq).elim id id
    simp [nullGauss,flipNullY,h2]
  · rw [null_gauss_inverse_eq hp hplus]
    unfold nullGauss
    rw [flipNullY_minus]
    change p 2/nullHorizontalPlus p = -(-p 2/nullHorizontalPlus p)
    rw [neg_div,neg_neg]

theorem null_gauss_flip_log_derivative {L : PeriodPair} {p : ℂ → Fin 3 → ℂ}
    (hp : TwoAxisNullDifferential L p)
    {z : ℂ} (hz : z ∉ L.lattice)
    (hanalytic : ∀ j, AnalyticAt ℂ (fun w => p w j) z) (h2 : p z 2 ≠ 0) :
    deriv (fun w => nullGauss (flipNullY (p w))) z/nullGauss (flipNullY (p z)) =
      -(deriv (fun w => nullGauss (p w)) z/nullGauss (p z)) := by
  let g : ℂ → ℂ := fun w => nullGauss (p w)
  have hm := (null_horizontal_nonzero_of_height (hp.null z hz) h2).1
  have hg : DifferentiableAt ℂ g z :=
    ((hanalytic 2).div (null_horizontal_minus_analyticAt hanalytic) hm).differentiableAt
  have hgn : g z ≠ 0 := div_ne_zero h2 hm
  have he : (fun w => nullGauss (flipNullY (p w))) =ᶠ[𝓝 z] (fun w => -(g w)⁻¹) := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact flipNullY_gauss_inverse (hp.null w hw)
  have hd := ((hg.hasDerivAt.inv hgn).neg).congr_of_eventuallyEq he
  have he0 : nullGauss (flipNullY (p z)) = -(g z)⁻¹ := he.self_of_nhds
  rw [hd.deriv,he0]
  change (-(-deriv g z/(g z)^2))/(-(g z)⁻¹) = -(deriv g z/g z)
  field_simp

/-- A fixed ambient reflection in the y-coordinate, if needed, places the
simple Gauss zero at the normalized positive height zero. -/
theorem exists_oriented_null_gauss_data {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1)
    {p : ℂ → Fin 3 → ℂ} (hp : TwoAxisNullDifferential (rhombicPeriodPair t ht) p)
    (hanalytic : ∀ z ∉ (rhombicPeriodPair t ht).lattice, ∀ j, AnalyticAt ℂ (fun w => p w j) z)
    {K : ℂ} (hK : K ≠ 0)
    (hheight : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      p z 2 = K*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a)) :
    ∃ q : ℂ → Fin 3 → ℂ, (q = p ∨ q = fun z => flipNullY (p z)) ∧
      GaussZeroPoleData t a ht (fun z => nullGauss (q z)) := by
  have han := real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2])
  rcases null_horizontal_not_both_zero (hp.null a han) (hp.regular a han) with hm | hp'
  · exact ⟨p,Or.inl rfl,null_gauss_zero_pole_data ht ha hp hanalytic hK hheight hm⟩
  · refine ⟨fun z => flipNullY (p z),Or.inr rfl,?_⟩
    apply null_gauss_zero_pole_data ht ha (flipNullY_two_axis hp)
      (fun z hz => flipNullY_analyticAt (hanalytic z hz)) hK
      (fun z hz => hheight z hz)
    rwa [flipNullY_minus]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.exists_oriented_null_gauss_data
#print axioms TwoAxisHelicoid.null_gauss_flip_log_derivative
