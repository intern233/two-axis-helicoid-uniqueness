import TwoAxisHelicoid.CompactChartExtension
import TwoAxisHelicoid.ActualAreaVariationIndex

namespace TwoAxisHelicoid
open Complex Set Function Filter
open scoped Topology ContDiff Manifold

/-- Translate the Euclidean parameters of a normal test into the actual
complex exterior chart. Its inverse records both real coordinates. -/
noncomputable def translatedPlaneCoordinates (c : ℂ) : (ℝ × ℝ) ≃ₜ ℂ :=
  equivRealProdCLM.symm.toHomeomorph.trans (Homeomorph.addRight c)

theorem translatedPlaneCoordinates_apply (c : ℂ) (p : ℝ × ℝ) :
    translatedPlaneCoordinates c p = planeComplex p+c := by
  apply congrArg (·+c)
  apply Complex.ext
  · exact (planeComplex_re p).symm
  · exact (planeComplex_im p).symm

/-- Global compact test functions agreeing with the plane tests at every
point where the exterior coordinates are defined. Independence includes
the case of the zero-dimensional family. -/
theorem exterior_chart_global_tests {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] (e : OpenPartialHomeomorph M ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) (c : ℂ) {n : ℕ}
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (ht : ∀ p ∈ K, translatedPlaneCoordinates c p ∈ e.target)
    (v : Fin n → ℝ × ℝ → ℝ) (hv : ∀ i, ContDiff ℝ ∞ (v i) ∧ tsupport (v i) ⊆ K)
    (hl : LinearIndependent ℝ v) :
    ∃ U : Fin n → M → ℝ, (∀ i, ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ) ∞ (U i) ∧
          tsupport (U i) ⊆ e.symm '' (translatedPlaneCoordinates c '' K)) ∧
      LinearIndependent ℝ U ∧ ∀ i p, translatedPlaneCoordinates c p ∈ e.target →
          U i (e.symm (translatedPlaneCoordinates c p)) = v i p := by
  classical
  let T := translatedPlaneCoordinates c
  let u (i : Fin n) := v i ∘ T.symm
  let U (i : Fin n) := compactChartExtend e (u i)
  have hk := hK.image T.continuous
  have ht' : T '' K ⊆ e.target := by rintro _ ⟨p,hp,rfl⟩; exact ht p hp
  have hs (i : Fin n) : tsupport (u i) ⊆ T '' K := by
    apply closure_minimal ?_ hk.isClosed
    intro z hz
    have hne : v i (T.symm z) ≠ 0 := hz
    exact ⟨_,(hv i).2 (subset_closure hne),T.apply_symm_apply z⟩
  have hu (i : Fin n) : ContDiff ℝ ∞ (u i) := by
    apply (hv i).1.comp
    exact equivRealProdCLM.contDiff.comp (contDiff_id.sub contDiff_const)
  have hval i p (hp : T p ∈ e.target) : U i (e.symm (T p)) = v i p :=
    (compactChartExtend_symm e (u i) hp).trans (congrArg (v i) (T.symm_apply_apply p))
  refine ⟨U,fun i => ⟨compactChartExtend_smooth e (hu i) (fun _ hx => holomorphic_chart_real_contMDiffAt he hx) hk ht' (hs i),
    (compactChartExtend_support e hk ht' (hs i)).2⟩,?_,hval⟩
  apply Fintype.linearIndependent_iff.mpr
  intro a ha
  apply Fintype.linearIndependent_iff.mp hl a
  funext p
  by_cases hp : p ∈ K
  · simpa only [Finset.sum_apply,Pi.smul_apply,hval _ p (ht p hp),Pi.zero_apply] using congrFun ha (e.symm (T p))
  · have hzero (i : Fin n) : v i p = 0 := by
      by_contra hn
      exact hp ((hv i).2 (subset_closure hn))
    simp [Finset.sum_apply,hzero]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.exterior_chart_global_tests
