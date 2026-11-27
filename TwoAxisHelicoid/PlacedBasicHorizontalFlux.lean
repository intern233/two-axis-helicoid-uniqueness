import TwoAxisHelicoid.AffineSlopingGeneratorFlux
import TwoAxisHelicoid.SlopingFluxIndependence
import TwoAxisHelicoid.AmbientHarmonicImmersion

namespace TwoAxisHelicoid
open Complex Matrix Set Filter
open scoped Topology

/-- A translated, rotated or rescaled closed basic torus has a genuine
nonvertical conormal loop in its new spatial frame. The two independent
period vectors prevent an arbitrary tilt from losing the conclusion. -/
theorem placed_basic_torus_has_horizontal_flux {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) (hc : c≠0)
    (X : PuncturedPeriodTorus (rhombicPeriodPair t ht) → Fin 3 → ℝ)
    (conf : ∀ z∉(rhombicPeriodPair t ht).lattice, ConformalCoordinateDerivatives (puncturedTorusPullback _ X) z)
    (hd : HasTwoAxisHelicoidCoordinateDifferential (puncturedTorusPullback _ X) t a c ht)
    (T : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)) (ho : ∀ x y, T x ⬝ᵥ T y=x ⬝ᵥ y) (b : Fin 3 → ℝ) {k : ℝ} (hk : k≠0) :
    HasSpatialNonverticalFlux (rhombicPeriodPair t ht) (fun q => b+k • T (X q)) := by
  let L := rhombicPeriodPair t ht
  let Z := fun q => b+k • T (X q)
  let R := k • T.toContinuousLinearEquiv.toContinuousLinearMap
  let V := puncturedTorusPullback L X
  let W := puncturedTorusPullback L Z
  have germ (z : ℂ) (off : z∉L.lattice) : W=ᶠ[𝓝 z] fun x => b+k • T (V x) := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds off] with x hx
    change x∉L.lattice at hx
    simp [V,W,Z,puncturedTorusPullback,hx]
  have d (z : ℂ) (off : z∉L.lattice) : HasFDerivAt W (R.comp (nullRealDerivative (coordinateData t a c ht z))) z := by
    have der := (((T.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp z (hd _ off)).const_smul k).const_add b)
    exact der.congr_of_eventuallyEq (germ _ off)
  have reg (z : ℂ) (off : z∉L.lattice) : ConformalCoordinateDerivatives W z := by
    apply (conformalCoordinateDerivatives_iff_dot (d _ off).differentiableAt).mpr
    obtain ⟨len,orth⟩ := (conformalCoordinateDerivatives_iff_dot (hd _ off).differentiableAt).mp (conf _ off)
    rw [(hd _ off).fderiv] at len orth
    rw [(d _ off).fderiv]
    let D := nullRealDerivative (coordinateData t a c ht z)
    change (k • T (D 1)) ⬝ᵥ (k • T (D 1)) = (k • T (D I)) ⬝ᵥ (k • T (D I)) ∧
      (k • T (D 1)) ⬝ᵥ (k • T (D I)) = 0
    change D 1 ⬝ᵥ D 1 = D I ⬝ᵥ D I at len
    change D 1 ⬝ᵥ D I = 0 at orth
    simp only [smul_dotProduct,dotProduct_smul,smul_eq_mul,ho,len,orth,mul_zero,and_self]
  let v := fun j => (originalCoordinatePeriod t a c ht j).im
  let w := fun j => (conjugateCoordinatePeriod t a c ht j).im
  obtain ⟨hG,_⟩ := periodic_actual_primitive_period_equations ht ha hc hd (fun z _ p hp => puncturedTorusPullback_periodic _ X z p hp)
  have neg := (closed_basic_data_sloping_bound ht ha hc X hd).trans_lt (by norm_num : -(1/32:ℝ)<0)
  have independent := flux_pair_independent_of_minor (v := v) (w := w) (sloping_generator_flux_minor_ne_zero ht ha hc hG neg.ne)
  obtain ⟨⟨q,γ,hγ⟩,q',δ,hδ⟩ := affine_sloping_generators_actual_fluxes ht Z R d reg
  rcases independent_flux_pair_has_horizontal_component independent T with ⟨j,jh,n⟩|⟨j,jh,n⟩
  · exact ⟨q,γ,j,R v j,jh,hγ j,mul_ne_zero hk n⟩
  · exact ⟨q',δ,j,R w j,jh,hδ j,mul_ne_zero hk n⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.placed_basic_torus_has_horizontal_flux
