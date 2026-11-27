import TwoAxisHelicoid.VerticalFluxTorusCrossing
import TwoAxisHelicoid.MinimalChartComplexData

namespace TwoAxisHelicoid
open Complex Set Filter Topology InnerProductSpace
open scoped Topology

private noncomputable def mixFirst (k : ℝ) : ℝ := (4*k⁻¹-k)/3
private noncomputable def mixSecond (k : ℝ) : ℝ := (2*k-2*k⁻¹)/3

/-- The positive real López–Ros orbit is a linear combination of the
positions at multipliers one and two in the horizontal plane. -/
noncomputable def realLopezRosPosition (k : ℝ) (X V : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![mixFirst k*X 0+mixSecond k*V 0,mixFirst k*X 1+mixSecond k*V 1,X 2]

private theorem mix_coefficients (k : ℝ) (p : Fin 3 → ℂ) (j : Fin 2) :
    (mixFirst k:ℂ)*p j.castSucc+(mixSecond k:ℂ)*lopezRosCoefficients 2 p j.castSucc =
      lopezRosCoefficients (k:ℂ) p j.castSucc := by
  fin_cases j <;> simp [lopezRosCoefficients,lopezRosHorizontal,lopezRosAverage,lopezRosSkew,mixFirst,mixSecond]
    <;> ring

private theorem mix_real_derivatives (k : ℝ) (p : Fin 3 → ℂ) (v : ℂ) (j : Fin 2) :
    mixFirst k*nullRealDerivative p v j.castSucc+mixSecond k*nullRealDerivative (lopezRosCoefficients 2 p) v j.castSucc =
      nullRealDerivative (lopezRosCoefficients (k:ℂ) p) v j.castSucc := by
  rw [nullRealDerivative_apply,nullRealDerivative_apply,nullRealDerivative_apply,← mix_coefficients k p j]
  rw [mul_add,mul_left_comm v (mixFirst k:ℂ),mul_left_comm v (mixSecond k:ℂ),Complex.add_re]
  simp

private theorem analytic_real_lopez_ros_position {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E} {k : E → ℝ} {X V : E → Fin 3 → ℝ} (hk : AnalyticAt ℝ k x) (hne : k x ≠ 0)
    (hX : AnalyticAt ℝ X x) (hV : AnalyticAt ℝ V x) :
    AnalyticAt ℝ (fun w => realLopezRosPosition (k w) (X w) (V w)) x := by
  have hrs : AnalyticAt ℝ (mixFirst ∘ k) x := ((analyticAt_const.mul (hk.inv hne)).sub hk).div_const (c := (3:ℝ))
  have hss : AnalyticAt ℝ (mixSecond ∘ k) x := ((analyticAt_const.mul hk).sub (analyticAt_const.mul (hk.inv hne))).div_const (c := (3:ℝ))
  have xj := analyticAt_pi_iff.mp hX
  have vj := analyticAt_pi_iff.mp hV
  apply analyticAt_pi_iff.mpr
  intro j
  fin_cases j
  · exact (hrs.mul (xj 0)).add (hss.mul (vj 0))
  · exact (hrs.mul (xj 1)).add (hss.mul (vj 1))
  · exact xj 2

/-- Under vertical flux choose one globally defined real deformation,
with joint real analyticity in the multiplier and the lifted surface
point. It has the required actual Weierstrass derivative for every
nonzero real multiplier. No continuity of choices of primitives in the
parameter is assumed. -/
theorem vertical_flux_joint_analytic_family (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (hX : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L X w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L X) z ∧ Function.Injective (fderiv ℝ (puncturedTorusPullback L X) z))
    (flux : ¬ HasIntrinsicNonverticalFlux L X) :
    ∃ Y : ℝ → PuncturedPeriodTorus L → Fin 3 → ℝ, Y 1=X ∧ (∀ k q, Y k q 2=X q 2) ∧
      ∀ k ≠ 0, ∀ z ∉ L.lattice,
        AnalyticAt ℝ (fun u : ℝ × ℂ => puncturedTorusPullback L (Y u.1) u.2) (k,z) ∧
        (∀ j, HarmonicAt (fun w => puncturedTorusPullback L (Y k) w j) z) ∧
        ConformalCoordinateDerivatives (puncturedTorusPullback L (Y k)) z ∧
        Function.Injective (fderiv ℝ (puncturedTorusPullback L (Y k)) z) ∧
        HasFDerivAt (puncturedTorusPullback L (Y k)) (nullRealDerivative (lopezRosCoefficients (k:ℂ) (torusImmersionForms L X z))) z := by
  obtain ⟨V,_,_,hV⟩ := vertical_flux_lopez_ros_immersions L X hX flux
  let Y (k : ℝ) (q : PuncturedPeriodTorus L) := realLopezRosPosition k (X q) (V 2 q)
  let P := puncturedTorusPullback L X
  let Q := puncturedTorusPullback L (V 2)
  have eq (k : ℝ) (z : ℂ) : puncturedTorusPullback L (Y k) z = realLopezRosPosition k (P z) (Q z) := by
    by_cases hn : z ∉ L.lattice
    · simp [puncturedTorusPullback,hn,Y,P,Q]
    · funext j
      fin_cases j <;> simp [puncturedTorusPullback,hn,realLopezRosPosition,P,Q]
  refine ⟨Y,?_,fun _ _ => rfl,?_⟩
  · funext q j
    fin_cases j <;> norm_num [Y,realLopezRosPosition,mixFirst,mixSecond]
  · intro k hk z hz
    have v2 := hV 2 (by norm_num) z hz
    have vk := hV (k:ℂ) (Complex.ofReal_ne_zero.mpr hk) z hz
    have hP : AnalyticAt ℝ P z := analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt ((hX z hz).1 j)
    have hQ : AnalyticAt ℝ Q z := analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (v2.1 j)
    let p := torusImmersionForms L X z
    have dP : HasFDerivAt P (nullRealDerivative p) z := immersionComplexCoefficient_hasFDerivAt hP.differentiableAt
    have dQ : HasFDerivAt Q (nullRealDerivative (lopezRosCoefficients 2 p)) z := v2.2.2.2
    have d (j : Fin 2) : HasFDerivAt (fun w => mixFirst k*P w j.castSucc+mixSecond k*Q w j.castSucc)
        ((ContinuousLinearMap.proj j.castSucc).comp (nullRealDerivative (lopezRosCoefficients (k:ℂ) p))) z := by
      let pr := (ContinuousLinearMap.proj j.castSucc : (Fin 3 → ℝ) →L[ℝ] ℝ)
      have h := ((pr.hasFDerivAt.comp z dP).const_smul (mixFirst k)).add ((pr.hasFDerivAt.comp z dQ).const_smul (mixSecond k))
      have same : mixFirst k • (pr.comp (nullRealDerivative p))+mixSecond k • (pr.comp (nullRealDerivative (lopezRosCoefficients 2 p))) = pr.comp (nullRealDerivative (lopezRosCoefficients (k:ℂ) p)) := by
        ext v
        exact mix_real_derivatives k p v j
      exact same ▸ h
    have dw : HasFDerivAt (puncturedTorusPullback L (Y k)) (nullRealDerivative (lopezRosCoefficients (k:ℂ) p)) z := by
      rw [funext (eq k)]
      apply hasFDerivAt_pi''
      intro j
      fin_cases j
      · exact d 0
      · exact d 1
      · let pr := (ContinuousLinearMap.proj 2 : (Fin 3 → ℝ) →L[ℝ] ℝ)
        have same : pr.comp (nullRealDerivative p) = pr.comp (nullRealDerivative (lopezRosCoefficients (k:ℂ) p)) := by ext v; rfl
        exact same ▸ (pr.hasFDerivAt.comp z dP)
    have harm (j : Fin 2) : HarmonicAt (fun w => mixFirst k*P w j.castSucc+mixSecond k*Q w j.castSucc) z :=
      (((hX z hz).1 j.castSucc).const_smul (c := mixFirst k)).add ((v2.1 j.castSucc).const_smul (c := mixSecond k))
    have equal : fderiv ℝ (puncturedTorusPullback L (Y k)) z = fderiv ℝ (puncturedTorusPullback L (V (k:ℂ))) z :=
      dw.fderiv.trans vk.2.2.2.fderiv.symm
    refine ⟨?_,?_,?_,by rw [equal]; exact vk.2.2.1,dw⟩
    · have fst : AnalyticAt ℝ (Prod.fst : ℝ × ℂ → ℝ) (k,z) := (ContinuousLinearMap.fst ℝ ℝ ℂ).analyticAt _
      have snd : AnalyticAt ℝ (Prod.snd : ℝ × ℂ → ℂ) (k,z) := (ContinuousLinearMap.snd ℝ ℝ ℂ).analyticAt _
      have joint := analytic_real_lopez_ros_position fst hk (hP.comp snd) (hQ.comp snd)
      exact joint.congr (Eventually.of_forall fun u => (eq u.1 u.2).symm)
    · rw [funext (eq k)]
      intro j
      fin_cases j
      · exact harm 0
      · exact harm 1
      · exact (hX z hz).1 2
    · apply (conformalCoordinateDerivatives_iff_dot dw.differentiableAt).mpr
      rw [equal]
      exact (conformalCoordinateDerivatives_iff_dot vk.2.2.2.differentiableAt).mp vk.2.1

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.vertical_flux_joint_analytic_family
