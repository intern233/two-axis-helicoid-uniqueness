import TwoAxisHelicoid.ConformalCoordinateLaplacian

namespace TwoAxisHelicoid
open Complex Matrix Filter InnerProductSpace Laplacian
open scoped Topology
set_option maxHeartbeats 1000000

theorem conformal_frame_orthogonal_eq_zero {A B V : Fin 3 → ℝ} {g : ℝ}
    (hg : 0 < g) (hA : A ⬝ᵥ A = g) (hB : B ⬝ᵥ B = g)
    (hAB : A ⬝ᵥ B = 0) (hVA : V ⬝ᵥ A = 0) (hVB : V ⬝ᵥ B = 0)
    (hVN : V ⬝ᵥ unitCrossNormal A B = 0) : V = 0 := by
  have hcross : (A ⨯₃ B) ⬝ᵥ (A ⨯₃ B) = g^2 := by
    rw [cross_dot_cross,hA,hB,hAB,zero_mul,sub_zero,pow_two]
  have hVN' : V ⬝ᵥ (A ⨯₃ B) = 0 := by
    have hh : g⁻¹*(V ⬝ᵥ (A ⨯₃ B)) = 0 := by
      simpa only [unitCrossNormal,dotProduct_smul,hcross,Real.sqrt_sq hg.le,smul_eq_mul]
        using hVN
    exact (mul_eq_zero.mp hh).resolve_left (inv_ne_zero hg.ne')
  have hNV : (A ⨯₃ B) ⬝ᵥ V = 0 := by rw [dotProduct_comm,hVN']
  have hCV : (A ⨯₃ B) ⨯₃ V = 0 := by
    rw [cross_cross_eq_smul_sub_smul,dotProduct_comm A V,dotProduct_comm B V,hVA,hVB]
    simp
  have hh := cross_dot_cross (A ⨯₃ B) V (A ⨯₃ B) V
  rw [hCV,zero_dotProduct,hcross,hNV,hVN',mul_zero,sub_zero] at hh
  exact dotProduct_self_eq_zero.mp
    ((mul_eq_zero.mp hh.symm).resolve_left (pow_ne_zero 2 hg.ne'))

/-- In a regular conformal chart the standard scalar mean curvature is
the normal component of the actual coordinate Laplacian divided by 2g. -/
theorem conformal_coordinate_mean_curvature_formula {X : ℂ → Fin 3 → ℝ}
    {z : ℂ} {g : ℝ} (hg : g ≠ 0)
    (hA : fderiv ℝ X z 1 ⬝ᵥ fderiv ℝ X z 1 = g)
    (hB : fderiv ℝ X z I ⬝ᵥ fderiv ℝ X z I = g)
    (hAB : fderiv ℝ X z 1 ⬝ᵥ fderiv ℝ X z I = 0) :
    coordinateMeanCurvature X z =
      ((Δ X z) ⬝ᵥ unitCrossNormal (fderiv ℝ X z 1) (fderiv ℝ X z I))/(2*g) := by
  unfold coordinateMeanCurvature
  dsimp only
  rw [hA,hB,hAB,laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [mul_zero,zero_mul,sub_zero,add_dotProduct,zero_pow two_ne_zero]
  field_simp

/-- This is the reverse direction needed for the original geometric
surface: zero actual mean curvature implies zero coordinate Laplacian,
once a genuine regular conformal chart is available. -/
theorem conformal_minimal_coordinate_laplacian_zero
    {X : ℂ → Fin 3 → ℝ} {z : ℂ} (hX : ContDiffAt ℝ 2 X z)
    (hc : ∀ᶠ w in 𝓝 z,
      fderiv ℝ X w 1 ⬝ᵥ fderiv ℝ X w 1 = fderiv ℝ X w I ⬝ᵥ fderiv ℝ X w I ∧
      fderiv ℝ X w 1 ⬝ᵥ fderiv ℝ X w I = 0)
    (hi : Function.Injective (fderiv ℝ X z))
    (hm : coordinateMeanCurvature X z = 0) : Δ X z = 0 := by
  let g := fderiv ℝ X z 1 ⬝ᵥ fderiv ℝ X z 1
  have hA : fderiv ℝ X z 1 ⬝ᵥ fderiv ℝ X z 1 = g := rfl
  have hg : 0 < g := by
    have hnonneg : 0 ≤ g := Finset.sum_nonneg (fun j _ => mul_self_nonneg _)
    apply lt_of_le_of_ne hnonneg
    intro he
    have hz : fderiv ℝ X z 1 = 0 := dotProduct_self_eq_zero.mp he.symm
    have h10 : (1 : ℂ) = 0 := hi (hz.trans (fderiv ℝ X z).map_zero.symm)
    exact one_ne_zero h10
  obtain ⟨hcon,horth⟩ := hc.self_of_nhds
  have hB : fderiv ℝ X z I ⬝ᵥ fderiv ℝ X z I = g := hcon.symm
  have hnormal : (Δ X z) ⬝ᵥ unitCrossNormal (fderiv ℝ X z 1) (fderiv ℝ X z I) = 0 := by
    rw [conformal_coordinate_mean_curvature_formula hg.ne' hA hB horth] at hm
    exact (div_eq_zero_iff.mp hm).resolve_right (mul_ne_zero two_ne_zero hg.ne')
  obtain ⟨hTA,hTB⟩ := conformal_coordinate_laplacian_tangent_orthogonal hX hc
  exact conformal_frame_orthogonal_eq_zero hg hA hB horth hTA hTB hnormal

/-- A C² minimal immersion is harmonic in every regular conformal
coordinate chart. This does not assert existence of such charts. -/
theorem conformal_minimal_harmonicAt {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hX : ContDiffAt ℝ 2 X z)
    (hc : ∀ᶠ w in 𝓝 z,
      fderiv ℝ X w 1 ⬝ᵥ fderiv ℝ X w 1 = fderiv ℝ X w I ⬝ᵥ fderiv ℝ X w I ∧
      fderiv ℝ X w 1 ⬝ᵥ fderiv ℝ X w I = 0)
    (hi : ∀ᶠ w in 𝓝 z, Function.Injective (fderiv ℝ X w))
    (hm : ∀ᶠ w in 𝓝 z, coordinateMeanCurvature X w = 0) : HarmonicAt X z := by
  refine ⟨hX,?_⟩
  filter_upwards [hX.eventually (by norm_num),eventually_eventually_nhds.mpr hc,hi,hm]
    with w hw hc' hi' hm'
  exact conformal_minimal_coordinate_laplacian_zero hw hc' hi' hm'

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.conformal_minimal_harmonicAt
