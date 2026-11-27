import TwoAxisHelicoid.MarkedExteriorGaussDivisor

namespace TwoAxisHelicoid
open Complex Filter Set Topology InnerProductSpace
open scoped Topology Manifold ContDiff

universe u

/-- An actual conformal one-handle surface with the exterior height and
Gauss formulas admits a marking with exactly one simple interior zero
and one simple interior pole. With vertical flux its López–Ros family
on the original carrier crosses in every neighborhood of that zero for
all sufficiently large positive multipliers. -/
theorem original_exterior_lopez_ros_eventual_crossing {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    {L₀ : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L₀)
    (uniform : CompactGenusOneUniformization.{u} L₀)
    (X : M → Fin 3 → ℝ) (hX : IsClosedEmbedding X) (hchart : ∀ d ∈ atlas ℂ M, HarmonicImmersionChart X d)
    (A : GeometricExteriorCoordinate X) :
    ∃ (L : PeriodPair) (f : M ≃ₜ PuncturedPeriodTorus L) (Y : PuncturedPeriodTorus L → Fin 3 → ℝ)
      (a b : ℂ) (ha : a ∉ L.lattice),
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f.symm ∧
      (∀ p, Y (f p) = X p) ∧ MarkedHelicoidalEndForms L Y ∧ OneEndInteriorGaussDivisor L (torusImmersionForms L Y) a b ∧
      (¬ HasIntrinsicNonverticalFlux L Y → ∃ W : ℂ → M → Fin 3 → ℝ,
        W 1 = X ∧ (∀ k p, W k p 2 = X p 2) ∧
        (∀ k ≠ 0, ∀ z ∉ L.lattice,
          (∀ j, HarmonicAt (fun w => puncturedTorusPullback L (W k ∘ f.symm) w j) z) ∧
          ConformalCoordinateDerivatives (puncturedTorusPullback L (W k ∘ f.symm)) z ∧
          Function.Injective (fderiv ℝ (puncturedTorusPullback L (W k ∘ f.symm)) z) ∧
          HasFDerivAt (puncturedTorusPullback L (W k ∘ f.symm)) (nullRealDerivative (lopezRosCoefficients k (torusImmersionForms L Y z))) z) ∧
        ∀ U ∈ 𝓝 (f.symm (puncturedPlaneProjection L ⟨a,ha⟩)), ∀ᶠ k : ℝ in atTop,
          ∃ p ∈ U, ∃ q ∈ U, p ≠ q ∧ W (k:ℂ) p = W (k:ℂ) q) := by
  obtain ⟨L,f,Y,hf,hi,eq,_,endData⟩ := original_exterior_surface_marked_end_forms top uniform X hX hchart A
  obtain ⟨κ,R,_,hR,hlog⟩ := endData.gauss_expansion
  have data := torusImmersionForms_regular L Y (fun z hz => (endData.regular z hz).1)
    (fun z hz => (endData.regular z hz).2.1)
  have nz (z : ℂ) (hz : z ∉ L.lattice) : torusImmersionForms L Y z ≠ 0 :=
    immersionComplexCoefficient_regular (analyticAt_pi_iff.mpr (fun j =>
      _root_.HarmonicAt.analyticAt ((endData.regular z hz).1 j))).differentiableAt (endData.regular z hz).2.2
  obtain ⟨a,b,d⟩ := one_end_torus_has_simple_gauss_divisor L (torusImmersionForms L Y) data.1
    (torusImmersionForms_periodic L Y) data.2.1 nz endData.height_order hR hlog
  refine ⟨L,f,Y,a,b,d.zero_regular,hf,hi,eq,endData,d,?_⟩
  intro flux
  obtain ⟨V,h1,hh,hV⟩ := vertical_flux_lopez_ros_immersions L Y endData.regular flux
  let W := fun k : ℂ => V k ∘ f
  have back (k : ℂ) : W k ∘ f.symm = V k := funext fun q => congrArg (V k) (f.apply_symm_apply q)
  refine ⟨W,?_,?_,?_,?_⟩
  · exact funext fun p => (congrFun h1 (f p)).trans (eq p)
  · exact fun k p => (hh k (f p)).trans (congrFun (eq p) 2)
  · intro k hk
    rw [back]
    exact hV k hk
  · intro U hU
    have hn := f.symm.continuous.continuousAt.preimage_mem_nhds hU
    have cross := lopez_ros_torus_position_eventually_not_injective L Y
      (fun z hz => ⟨(endData.regular z hz).1,(endData.regular z hz).2.1⟩)
      d.zero_regular d.minus_nonzero d.height_zero d.simple_height_zero (fun k : ℝ => V (k:ℂ))
      (fun k hk z hz => (hV _ (Complex.ofReal_ne_zero.mpr hk.ne') z hz).2.2.2) hn
    filter_upwards [cross] with k hk
    obtain ⟨p,hp,q,hq,hne,he⟩ := hk
    exact ⟨f.symm p,hp,f.symm q,hq,fun h => hne (f.symm.injective h),by simpa [W] using he⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_exterior_lopez_ros_eventual_crossing
