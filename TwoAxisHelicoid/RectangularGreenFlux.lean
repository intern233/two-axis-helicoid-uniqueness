import TwoAxisHelicoid.AnalyticPlaneLaplacian
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

namespace TwoAxisHelicoid
open Complex Set MeasureTheory InnerProductSpace Laplacian
open scoped Interval ContDiff

/-- Outward flux through the four oriented sides of a parameter rectangle. -/
noncomputable def rectangleOutwardFlux (a b : ℝ×ℝ) (P Q : ℂ → ℝ) : ℝ :=
  let E := Complex.equivRealProdCLM.symm
  (((∫ x in a.1..b.1, Q (E (x,b.2)))-(∫ x in a.1..b.1, Q (E (x,a.2))))+
    (∫ y in a.2..b.2, P (E (b.1,y))))-(∫ y in a.2..b.2, P (E (a.1,y)))

/-- The actual outward side integrals of a C¹ vector field equal its
interior divergence on every closed rectangle. -/
theorem rectangle_outward_flux_eq_divergence (a b : ℝ×ℝ) (ordered : a≤b) {P Q : ℂ → ℝ}
    (cP : ∀ q∈Icc a b, ContDiffAt ℝ 1 P (Complex.equivRealProdCLM.symm q))
    (cQ : ∀ q∈Icc a b, ContDiffAt ℝ 1 Q (Complex.equivRealProdCLM.symm q)) :
    (∫ q in Icc a b, planePartial 1 P (Complex.equivRealProdCLM.symm q)+
      planePartial I Q (Complex.equivRealProdCLM.symm q))=rectangleOutwardFlux a b P Q := by
  let E := Complex.equivRealProdCLM.symm
  let dp := fun q => (fderiv ℝ P (E q)).comp E.toContinuousLinearMap
  let dq := fun q => (fderiv ℝ Q (E q)).comp E.toContinuousLinearMap
  have ex : E (1,0)=1 := by simp [E,Complex.equivRealProdCLM_symm_apply]
  have ey : E (0,1)=I := by simp [E,Complex.equivRealProdCLM_symm_apply]
  have xp (q : ℝ×ℝ) : dp q (1,0)=planePartial 1 P (E q) := congrArg (fderiv ℝ P (E q)) ex
  have yq (q : ℝ×ℝ) : dq q (0,1)=planePartial I Q (E q) := congrArg (fderiv ℝ Q (E q)) ey
  have inc {q : ℝ×ℝ} (hq : q∈Ioo a.1 b.1 ×ˢ Ioo a.2 b.2) : q∈Icc a b :=
    ⟨⟨hq.1.1.le,hq.2.1.le⟩,⟨hq.1.2.le,hq.2.2.le⟩⟩
  have cp {U : ℂ → ℝ} (j : ℂ) (cu : ∀ q∈Icc a b, ContDiffAt ℝ 1 U (E q)) :
      ContinuousOn (fun q => planePartial j U (E q)) (Icc a b) := by
    intro q hq
    exact (((cu q hq).continuousAt_fderiv one_ne_zero).clm_apply (continuousAt_const (y:=j)) |>.comp
      E.continuous.continuousAt).continuousWithinAt
  have integral : IntegrableOn (fun q => dp q (1,0)+dq q (0,1)) (Icc a b) := by
    simp only [xp,yq]
    exact ((cp 1 cP).add (cp I cQ)).integrableOn_compact isCompact_Icc
  have flux := integral_divergence_prod_Icc_of_hasFDerivAt_of_le (P ∘ E) (Q ∘ E) dp dq a b ordered
    (fun q hq => ((cP q hq).continuousAt.comp E.continuous.continuousAt).continuousWithinAt)
    (fun q hq => ((cQ q hq).continuousAt.comp E.continuous.continuousAt).continuousWithinAt)
    (fun q hq => ((cP q (inc hq)).differentiableAt one_ne_zero).hasFDerivAt.comp q E.hasFDerivAt)
    (fun q hq => ((cQ q (inc hq)).differentiableAt one_ne_zero).hasFDerivAt.comp q E.hasFDerivAt) integral
  simpa only [xp,yq,Function.comp_apply,rectangleOutwardFlux] using flux

theorem plane_partial_c1_of_c2 {u : ℂ → ℝ} {z : ℂ} (c : ContDiffAt ℝ 2 u z) (j : ℂ) :
    ContDiffAt ℝ 1 (planePartial j u) z :=
  (ContinuousLinearMap.apply ℝ ℝ j).contDiff.contDiffAt.comp z (c.fderiv_right (by norm_num))

theorem laplacian_plane_partials_c2 {u : ℂ → ℝ} {z : ℂ} (c : ContDiffAt ℝ 2 u z) :
    (Δ u) z=planePartial 1 (planePartial 1 u) z+planePartial I (planePartial I u) z := by
  have h (v : ℂ) : planePartial v (planePartial v u) z=fderiv ℝ (fderiv ℝ u) z v v := by
    have der := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp z
      ((c.fderiv_right (m:=1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
    change fderiv ℝ ((ContinuousLinearMap.apply ℝ ℝ v) ∘ fderiv ℝ u) z v=_
    rw [der.fderiv]
    rfl
  simp only [laplacian_eq_iteratedFDeriv_complexPlane,iteratedFDeriv_two_apply,h,Matrix.cons_val_zero,Matrix.cons_val_one]

/-- Integration by parts for a scalar Jacobi equation on a conformal
parameter rectangle. Both area and boundary sides are actual integrals. -/
theorem jacobi_green_rectangle_first (a b : ℝ×ℝ) (ordered : a≤b) {u v W : ℂ → ℝ}
    (cu : ∀ q∈Icc a b, ContDiffAt ℝ 1 u (Complex.equivRealProdCLM.symm q))
    (cv : ∀ q∈Icc a b, ContDiffAt ℝ 2 v (Complex.equivRealProdCLM.symm q))
    (eqv : ∀ q∈Icc a b, let z := Complex.equivRealProdCLM.symm q; (Δ v) z+W z*v z=0) :
    (∫ q in Icc a b, let z := Complex.equivRealProdCLM.symm q
      planePartial 1 u z*planePartial 1 v z+planePartial I u z*planePartial I v z-W z*u z*v z)=
      rectangleOutwardFlux a b (fun z => u z*planePartial 1 v z) (fun z => u z*planePartial I v z) := by
  let E := Complex.equivRealProdCLM.symm
  have sm (j : ℂ) (q : ℝ×ℝ) (hq : q∈Icc a b) :=
    (cu q hq).mul (plane_partial_c1_of_c2 (cv q hq) j)
  rw [← rectangle_outward_flux_eq_divergence a b ordered (sm 1) (sm I)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro q hq
  let z := E q
  have h : (Δ v) z+W z*v z=0 := eqv q hq
  rw [laplacian_plane_partials_c2 (cv q hq)] at h
  have deriv (j : ℂ) := planePartial_mul ((cu q hq).differentiableAt one_ne_zero)
    ((plane_partial_c1_of_c2 (cv q hq) j).differentiableAt one_ne_zero) j
  dsimp only
  rw [deriv 1,deriv I]
  linear_combination -(u z)*h

/-- The outward Wronskian flux of two solutions of the same Jacobi
equation vanishes on every conformal parameter rectangle. -/
theorem jacobi_green_rectangle_second (a b : ℝ×ℝ) (ordered : a≤b) {u v W : ℂ → ℝ}
    (cu : ∀ q∈Icc a b, ContDiffAt ℝ 2 u (Complex.equivRealProdCLM.symm q))
    (cv : ∀ q∈Icc a b, ContDiffAt ℝ 2 v (Complex.equivRealProdCLM.symm q))
    (equ : ∀ q∈Icc a b, let z := Complex.equivRealProdCLM.symm q; (Δ u) z+W z*u z=0)
    (eqv : ∀ q∈Icc a b, let z := Complex.equivRealProdCLM.symm q; (Δ v) z+W z*v z=0) :
    rectangleOutwardFlux a b (fun z => u z*planePartial 1 v z) (fun z => u z*planePartial I v z)-
      rectangleOutwardFlux a b (fun z => v z*planePartial 1 u z) (fun z => v z*planePartial I u z)=0 := by
  rw [← jacobi_green_rectangle_first a b ordered (fun q hq => (cu q hq).of_le (by norm_num)) cv eqv,
    ← jacobi_green_rectangle_first a b ordered (fun q hq => (cv q hq).of_le (by norm_num)) cu equ,sub_eq_zero]
  apply setIntegral_congr_fun measurableSet_Icc
  intro q _
  ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rectangle_outward_flux_eq_divergence
#print axioms TwoAxisHelicoid.jacobi_green_rectangle_first
#print axioms TwoAxisHelicoid.jacobi_green_rectangle_second
