import TwoAxisHelicoid.HelicoidCanonicalSpinExtension
import TwoAxisHelicoid.ExactHelicoidMarkedEnd
import TwoAxisHelicoid.PinkallHelicoidSpinParity

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped ContDiff Manifold
universe u

/-- Proposition 4.4 in a marked topological torus. The end hypothesis
requires smooth graph height tending to zero. The comparison of full spin
covers extends uniquely and the spatial quadratic form is even in every
symplectic basis. The only external hypothesis is the unmarked regular
homotopy theorem for closed embedded tori. -/
theorem height_decay_helicoidal_torus_unique_even_spin (hPinkall : PinkallEmbeddedTorusRegularHomotopy)
    (L : PeriodPair) {X : PeriodTorus L → Fin 3 → ℝ}
    (A : (Fin 3 → ℝ) ≃ₜ HelicoidTubeCoordinates) (hA : ContDiff ℝ ∞ A) (hAi : ContDiff ℝ ∞ A.symm)
    (hEnd : HasHelicoidHeightEnd (fun q : PuncturedPeriodTorus L => A (X q.1)))
    (hp : IsProperMap (fun q : PuncturedPeriodTorus L => X q.1))
    (hXi : Function.Injective (fun q : PuncturedPeriodTorus L => X q.1))
    (hsm : ∀ p ≠ 0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X p)
    (hi : ∀ p ≠ 0, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X p)) :
    HasUniqueGenuineCompactSpinExtension.{u} L X hsm hi (fun F =>
      ∀ v w, torusIntersectionModTwo v w = 1 →
        capAmbientSpinQuadratic L F v * capAmbientSpinQuadratic L F w = 0) ∧
      ∀ v w, torusIntersectionModTwo v w = 1 →
        capAmbientSpinQuadratic L X v * capAmbientSpinQuadratic L X w = 0 := by
  obtain ⟨B,hB,hBi,hE⟩ := helicoidal_height_end_admits_C1_chart
    (X := fun q : PuncturedPeriodTorus L => X q.1) A hA hAi hEnd hp
  refine ⟨?_,helicoidal_torus_marked_arf_zero_of_pinkall hPinkall L B hB hBi hE hp hXi hsm hi⟩
  obtain ⟨F,cs,hF,hiF,K,R,U,n,σ,β,hK,hU,hKU,hfx,hm,he,hcap,hcapi,hn,hng,hpt,hcov,hproj,hbase,hKσ,hrot,hu,_⟩ :=
    helicoidal_surface_unique_genuine_spin_extension.{u} L B hB hBi hE hp hXi hsm hi
  let _ := cs
  let _ := hm
  have hatlas (q : PeriodTorus L) (hq : q ≠ 0) :=
    common_immersion_structures_compatible (hF q hq) (hiF q hq) (hcap q) (hcapi q)
  have hzero := pinkall_even_on_punctured_marking hPinkall L F cs hm he hcap hcapi hatlas
  refine ⟨F,cs,hF,hiF,K,R,U,n,σ,β,hK,hU,hKU,hfx,hm,he,hcap,hcapi,hn,hng,hpt,hcov,hproj,hbase,hKσ,hrot,hu,?_⟩
  intro v w hvw
  rw [cap_ambient_arf_basis L F v w hvw]
  exact hzero



end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.height_decay_helicoidal_torus_unique_even_spin
