import TwoAxisHelicoid.ActualTorusImmersion
import TwoAxisHelicoid.ActualHeightEndOrder
import TwoAxisHelicoid.HarmonicTorusRigidityData

namespace TwoAxisHelicoid
open Complex Set Filter InnerProductSpace
open scoped Topology

/-- The harmonicity, conformality and exact height pole required by the
intrinsic Gauss rigidity theorem hold for the actual quotient primitive. -/
theorem actual_torus_rigidity_hypotheses {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0:ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0) (hH : thetaHorizontalPeriod t a = 0) :
    let L := rhombicPeriodPair t ht
    let X := fun q : PuncturedPeriodTorus L => actualTorusImmersion ht ha hc hG hH q.1
    (∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L X w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L X) z) ∧
      meromorphicOrderAt (fun z => torusImmersionForms L X z 2) 0 = (-2:ℤ) := by
  let L := rhombicPeriodPair t ht
  let X := fun q : PuncturedPeriodTorus L => actualTorusImmersion ht ha hc hG hH q.1
  let P := actualGlobalImmersion t a c ht
  have e (z : ℂ) (hz : z ∉ L.lattice) : puncturedTorusPullback L X =ᶠ[𝓝 z] P := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    change w ∉ L.lattice at hw
    simp [puncturedTorusPullback,hw,puncturedPlaneProjection,X,P,L]
  have H := actual_global_conformal_harmonic_immersion ht ha hc hG hH
  have d (z : ℂ) (hz : z ∉ L.lattice) := (H.2.2.2 z hz).1.congr_of_eventuallyEq (e z hz)
  constructor
  · intro z hz
    constructor
    · intro j
      exact (harmonicAt_congr_nhds ((e z hz).mono fun w hw => congrFun hw j)).mpr
        ((H.2.2.1 z hz).comp_CLM (ContinuousLinearMap.proj j))
    · have hj (j : Fin 3) : fderiv ℝ (fun w => puncturedTorusPullback L X w j) z =
          (ContinuousLinearMap.proj j).comp (nullRealDerivative (coordinateData t a c ht z)) :=
        ((ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp z (d z hz)).fderiv
      obtain ⟨_,h₁,h₂,h₃⟩ := nullRealDerivative_conformal (coordinateData_null ht ha hz) (coordinateData_ne_zero ht ha hc hz)
      change ConformalCoordinateDerivatives (puncturedTorusPullback L X) z
      unfold ConformalCoordinateDerivatives
      simp only [hj,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply]
      exact ⟨h₁.trans h₂.symm,h₃⟩
  · apply Eq.trans (meromorphicOrderAt_congr (f₂ := fun z => coordinateData t a c ht z 2) _)
      (actual_coordinate_height_double_pole ht hc)
    filter_upwards [nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0),self_mem_nhdsWithin] with z hz hz0
    have hL : z ∉ L.lattice := fun h => hz ⟨h,hz0⟩
    have he := (immersionComplexCoefficient_hasFDerivAt (d z hL).differentiableAt).unique (d z hL)
    change immersionComplexCoefficient (puncturedTorusPullback L X) z 2 = coordinateData t a c ht z 2
    apply Complex.ext
    · simpa using congrArg (fun f : ℂ →L[ℝ] (Fin 3 → ℝ) => f 1 2) he
    · simpa using congrArg (fun f : ℂ →L[ℝ] (Fin 3 → ℝ) => f I 2) he

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_torus_rigidity_hypotheses
