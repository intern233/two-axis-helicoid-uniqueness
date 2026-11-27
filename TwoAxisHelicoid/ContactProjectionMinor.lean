import TwoAxisHelicoid.RegularGraphCoordinates
import TwoAxisHelicoid.FirstContactTangentPlanes
import TwoAxisHelicoid.MinimalChartComplexData

namespace TwoAxisHelicoid
open Complex Set Matrix Filter Topology
open scoped ContDiff

/-- The real determinant of the projected tangent basis vanishes
exactly when the projection loses rank. -/
theorem coordinate_minor_of_projection_injective (D : ℂ →L[ℝ] (Fin 3 → ℝ)) (i j : Fin 3)
    (hinj : Function.Injective ((spatialGraphProjection i j).comp D)) :
    D 1 i*D I j-D 1 j*D I i ≠ 0 := by
  let P := (spatialGraphProjection i j).comp D
  intro zero
  have relation (v : ℂ) (h : (P 1).re*v.re+(P I).re*v.im=0)
      (k : (P 1).im*v.re+(P I).im*v.im=0) : v=0 := by
    apply hinj
    rw [map_zero,real_linear_complex_expansion P v]
    apply Complex.ext
    · simp only [Complex.add_re,Complex.smul_re,smul_eq_mul,Complex.zero_re]
      linarith only [h]
    · simp only [Complex.add_im,Complex.smul_im,smul_eq_mul,Complex.zero_im]
      linarith only [k]
  change (P 1).re*(P I).im-(P 1).im*(P I).re=0 at zero
  have eq₁ := relation ⟨-(P I).re,(P 1).re⟩ (by change _*(-_)+_*_=0; ring)
    (by change _*(-_)+_*_=0; linear_combination zero)
  have eq₂ := relation ⟨-(P I).im,(P 1).im⟩ (by change _*(-_)+_*_=0; linear_combination -zero)
    (by change _*(-_)+_*_=0; ring)
  have a : P 1=0 := Complex.ext (show (P 1).re=0 from congrArg Complex.im eq₁) (show (P 1).im=0 from congrArg Complex.im eq₂)
  exact one_ne_zero (hinj (a.trans P.map_zero.symm))

/-- If two regular sheets have the same tangent plane, one Cartesian
projection is nonsingular on both sheets. -/
theorem common_coordinate_minor_of_tangent_eq (A B : ℂ →L[ℝ] (Fin 3 → ℝ))
    (hi : Function.Injective A) (hj : Function.Injective B) (same : A.range=B.range) :
    ∃ σ : Equiv.Perm (Fin 3),
      A 1 (σ 0)*A I (σ 1)-A 1 (σ 1)*A I (σ 0) ≠ 0 ∧
      B 1 (σ 0)*B I (σ 1)-B 1 (σ 1)*B I (σ 0) ≠ 0 := by
  obtain ⟨i,j,ne,hm⟩ := regular_immersion_coordinate_minor A hi
  have perm : ∀ i j : Fin 3, i ≠ j → ∃ σ : Equiv.Perm (Fin 3), σ 0=i ∧ σ 1=j := by decide
  obtain ⟨σ,e₀,e₁⟩ := perm i j ne
  have inj := spatialGraphProjection_injective A i j hm
  let P := spatialGraphProjection i j
  have ib : Function.Injective (P.comp B) := by
    intro u v eq
    have lift (w : ℂ) : ∃ z, A z=B w := by
      change B w ∈ A.range
      rw [same]
      exact ⟨w,rfl⟩
    obtain ⟨x,hx⟩ := lift u
    obtain ⟨y,hy⟩ := lift v
    have h : x=y := inj (show P (A x)=P (A y) by rwa [hx,hy])
    exact hj (hx.symm.trans ((congrArg A h).trans hy))
  exact ⟨σ,by simpa only [e₀,e₁] using hm,by simpa only [e₀,e₁] using coordinate_minor_of_projection_injective B i j ib⟩

/-- Reindexing the three Cartesian coordinates preserves the
actual conformality equations. -/
theorem conformal_reindex_coordinates {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (σ : Equiv.Perm (Fin 3)) (hc : ConformalCoordinateDerivatives X z) :
    ConformalCoordinateDerivatives (fun w j => X w (σ j)) z := by
  obtain ⟨a,b⟩ := hc
  constructor
  · exact (Equiv.sum_comp σ (fun i => (fderiv ℝ (fun w => X w i) z 1)^2)).trans
      (a.trans (Equiv.sum_comp σ (fun i => (fderiv ℝ (fun w => X w i) z I)^2)).symm)
  · exact (Equiv.sum_comp σ (fun i => fderiv ℝ (fun w => X w i) z 1*fderiv ℝ (fun w => X w i) z I)).trans b

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.common_coordinate_minor_of_tangent_eq
#print axioms TwoAxisHelicoid.conformal_reindex_coordinates
