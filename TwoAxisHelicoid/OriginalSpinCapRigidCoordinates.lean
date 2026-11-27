import TwoAxisHelicoid.PinkallHelicoidSpinParity
import TwoAxisHelicoid.CoordinateOrientationIsometry
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped ContDiff Manifold

private theorem coordinate_isometry_smooth_both (R : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ))
    (hR : ∀ v w : Fin 3 → ℝ, (∑ j, (R v j-R w j)^2) = ∑ j, (v j-w j)^2) :
    ContDiff ℝ ∞ R ∧ ContDiff ℝ ∞ R.symm := by
  have smooth (J : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ))
      (hJ : ∀ v w : Fin 3 → ℝ, (∑ j, (J v j-J w j)^2) = ∑ j, (v j-w j)^2) :
      ContDiff ℝ ∞ J := by
    let C := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
    let E := (euclideanOrientationIsometry J hJ).toRealAffineIsometryEquiv
    have h : ContDiff ℝ ∞ E := E.toAffineIsometry.toContinuousAffineMap.contDiff
    exact C.contDiff.comp (h.comp C.symm.contDiff)
  refine ⟨smooth R hR,smooth R.symm fun v w => ?_⟩
  simpa only [R.apply_symm_apply] using (hR (R.symm v) (R.symm w)).symm

/-- Transport an actual smooth closed cap back into the original Euclidean
coordinates. Its inverse rigid placement has injective differential in
the same compact atlas, and its actual ambient spin is even in every
symplectic basis. -/
theorem rigid_coordinates_original_even_cap (pinkall : PinkallEmbeddedTorusRegularHomotopy)
    (L : PeriodPair) (F : PeriodTorus L → Fin 3 → ℝ) (cs : ChartedSpace (ℝ × ℝ) (PeriodTorus L))
    (R : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ))
    (hR : ∀ v w : Fin 3 → ℝ, (∑ j, (R v j-R w j)^2) = ∑ j, (v j-w j)^2) :
    let _ := cs
    IsManifold 𝓘(ℝ,ℝ × ℝ) ∞ (PeriodTorus L) → IsClosedEmbedding F →
    ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F →
    (∀ p, Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) F p)) →
    (∀ q ≠ 0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ × ℝ) ∞ (@id (PeriodTorus L)) q ∧
      ContMDiffAt 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,ℂ) ∞ (@id (PeriodTorus L)) q) →
    IsClosedEmbedding (R.symm ∘ F) ∧
    ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) ∞ (R.symm ∘ F) ∧
    (∀ p, Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) (R.symm ∘ F) p)) ∧
    ∀ v w, torusIntersectionModTwo v w = 1 →
      capAmbientSpinQuadratic L (R.symm ∘ F) v * capAmbientSpinQuadratic L (R.symm ∘ F) w = 0 := by
  intro inst hm he hf hfi hA
  obtain ⟨hs,hi⟩ := coordinate_isometry_smooth_both R hR
  let I := 𝓘(ℝ,Fin 3 → ℝ)
  have hd := hs.contMDiff
  have hd' := hi.contMDiff
  have hinj (v : Fin 3 → ℝ) : Function.Injective (mfderiv I I R.symm v) := by
    have h := mfderiv_comp v (hd.mdifferentiable (by simp) (R.symm v)) (hd'.mdifferentiable (by simp) v)
    rw [show (R ∘ R.symm : (Fin 3 → ℝ) → Fin 3 → ℝ) = id from funext R.apply_symm_apply,mfderiv_id] at h
    intro x y hxy
    exact (DFunLike.congr_fun h x).trans ((congrArg (mfderiv I I R (R.symm v)) hxy).trans (DFunLike.congr_fun h y).symm)
  have hc (p : PeriodTorus L) : Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) I (R.symm ∘ F) p) := by
    rw [mfderiv_comp p (hd'.mdifferentiable (by simp) (F p)) (hf.mdifferentiable (by simp) p)]
    exact (hinj _).comp (hfi _)
  have hE := R.symm.isClosedEmbedding.comp he
  have hF := hd'.comp hf
  have hzero := pinkall_even_on_punctured_marking pinkall L (R.symm ∘ F) cs hm hE hF hc hA
  exact ⟨hE,hF,hc,fun v w hvw => (cap_ambient_arf_basis L (R.symm ∘ F) v w hvw).trans hzero⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rigid_coordinates_original_even_cap
