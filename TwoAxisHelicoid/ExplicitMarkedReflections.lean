import TwoAxisHelicoid.CoordinateSignMaps
import TwoAxisHelicoid.CenteredActualImmersion
import TwoAxisHelicoid.RealCoefficientSymmetry

namespace TwoAxisHelicoid
open Complex Set Filter InnerProductSpace
open scoped ComplexConjugate Topology

private theorem centered_affine_symmetry {t : ℝ} (ht : 0<t) {X : ℂ → Fin 3 → ℝ}
    (D : ℂ → (ℂ →L[ℝ] (Fin 3 → ℝ))) (R : ℂ →L[ℝ] ℂ) (S : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))
    (diff : ∀ z∉(rhombicPeriodPair t ht).lattice, HasFDerivAt X (D z) z)
    (reg : ∀ z∉(rhombicPeriodPair t ht).lattice, R z∉(rhombicPeriodPair t ht).lattice)
    (forms : ∀ z, (D (R z)).comp R=S.comp (D z)) (base : X (R 1)=X 1) :
    ∀ z∉(rhombicPeriodPair t ht).lattice, X (R z)-X 1=S (X z-X 1) := by
  let L := rhombicPeriodPair t ht
  have f (z : ℂ) (hz : z∉L.lattice) := (diff _ (reg _ hz)).comp z R.hasFDerivAt
  have g (z : ℂ) (hz : z∉L.lattice) := S.hasFDerivAt.comp z (diff _ hz)
  obtain ⟨v,h⟩ := L.isClosed_lattice.isOpen_compl.exists_eq_add_of_fderiv_eq (rhombic_punctured_plane_isConnected ht).2
    (fun z hz => (f z hz).differentiableAt.differentiableWithinAt) (fun z hz => (g z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (f z hz).fderiv.trans ((forms z).trans (g z hz).fderiv.symm))
  have member : (1:ℂ) ∉ L.lattice := by
    simpa using real_not_mem_rhombic_lattice_of_pos ht (by norm_num : (0:ℝ)<1) (by norm_num)
  have one := h member
  change X (R 1)=S (X 1)+v at one
  rw [base] at one
  intro z hz
  have he : X (R z)=S (X z)+v := h hz
  rw [he,map_sub]
  calc
    S (X z)+v-X 1 = S (X z)+v-(S (X 1)+v) := congrArg (fun y => S (X z)+v-y) one
    _ = _ := by abel

theorem explicit_centered_primitive_reflections {t a c : ℝ} (ht : 0<t)
    {X : ℂ → Fin 3 → ℝ} (diff : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (per : ∀ z ω, ω∈(rhombicPeriodPair t ht).lattice → X (z+ω)=X z) :
    let F := fun z => X z-X 1
    ∀ z∉(rhombicPeriodPair t ht).lattice,
      F (-z)=![-F z 0,F z 1,-F z 2] ∧ F (conj z)=![F z 0,-F z 1,-F z 2] := by
  let C := coordinateData t a c ht
  let D := fun z => nullRealDerivative (C z)
  let N := -ContinuousLinearMap.id ℝ ℂ
  let S := coordinateSignMap ![-1,1,-1]
  let K := Complex.conjCLE.toContinuousLinearMap
  let T := coordinateSignMap ![1,-1,-1]
  have neg (z : ℂ) : (D (N z)).comp N=S.comp (D z) := by
    ext u j
    change ((-u)*C (-z) j).re=(![-1,1,-1] : Fin 3 → ℝ) j*(u*C z j).re
    rw [show C (-z)=_ from coordinateData_neg (a := a) (c := c) ht z]
    fin_cases j <;> simp [C]
  have conjugate (z : ℂ) : (D (K z)).comp K=T.comp (D z) := by
    ext u j
    change (conj u*C (conj z) j).re=(![1,-1,-1] : Fin 3 → ℝ) j*(u*C z j).re
    rw [show C (conj z)=_ from coordinateData_conj (a := a) (c := c) ht z]
    fin_cases j <;> simp [C,← map_mul]
  have nh : X (N 1)=X 1 := by
    have h := per (1:ℂ) (-2) ((rhombicPeriodPair t ht).lattice.neg_mem (rhombicPeriodPair t ht).ω₁_mem_lattice)
    change X (-(1:ℂ))=X 1
    convert h using 2
    norm_num
  have n := centered_affine_symmetry ht D N S diff (fun z hz => by change -z∉_; simpa using hz) neg nh
  have k := centered_affine_symmetry ht D K T diff (fun z hz h => hz (by
    change conj z ∈ _ at h
    simpa only [Complex.conj_conj] using rhombic_conj_mem ht h))
    conjugate (by change X (conj 1)=_; rw [map_one])
  dsimp only
  intro z hz
  constructor
  · apply (n z hz).trans
    ext j
    fin_cases j <;> simp [S]
  · apply (k z hz).trans
    ext j
    fin_cases j <;> simp [T]

/-- The explicit immersion at every closed parameter is an actual
two-axis harmonic conformal immersion in its original marked complex
plane coordinates, before any global injectivity argument. -/
theorem centered_closed_primitive_two_axis_immersion {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    (hc : c≠0) (v : thetaG t a=0) (h : thetaHorizontalPeriod t a=0) :
    TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) (centeredActualPrimitive t a c ht) := by
  let X := actualGlobalImmersion t a c ht
  have G := actual_global_conformal_harmonic_immersion ht ha hc v h
  have diff : HasTwoAxisHelicoidCoordinateDifferential X t a c ht := fun z hz => (G.2.2.2 z hz).1
  have sym := explicit_centered_primitive_reflections ht diff G.1
  have H (z : ℂ) (hz : z∉(rhombicPeriodPair t ht).lattice) := centeredActualPrimitive_hasFDerivAt ht ha hc v h hz
  refine ⟨fun z hz => (H z hz).differentiableAt,?_,?_,?_,?_,fun z hz => (sym z hz).1,fun z hz => (sym z hz).2⟩
  · intro z hz j
    have b := ((G.2.2.1 z hz).sub (harmonicAt_const (X 1))).comp_CLM
      (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ)
    exact b
  · intro z hz
    have hj (j : Fin 3) : fderiv ℝ (fun w => centeredActualPrimitive t a c ht w j) z =
        (ContinuousLinearMap.proj j).comp (nullRealDerivative (coordinateData t a c ht z)) :=
      ((ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp z (H z hz)).fderiv
    obtain ⟨_,h₁,h₂,h₃⟩ := nullRealDerivative_conformal (coordinateData_null ht ha hz) (coordinateData_ne_zero ht ha hc hz)
    unfold ConformalCoordinateDerivatives
    simp only [hj,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply]
    exact ⟨h₁.trans h₂.symm,h₃⟩
  · intro z hz
    rw [(H z hz).fderiv]
    exact nullRealDerivative_injective (coordinateData_null ht ha hz) (coordinateData_ne_zero ht ha hc hz)
  · intro z _ ω hω
    change X (z+ω)-X 1=X z-X 1
    exact congrArg (fun u => u-X 1) (G.1 z ω hω)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.explicit_centered_primitive_reflections
#print axioms TwoAxisHelicoid.centered_closed_primitive_two_axis_immersion
