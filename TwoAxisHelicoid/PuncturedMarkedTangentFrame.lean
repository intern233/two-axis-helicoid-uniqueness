import TwoAxisHelicoid.ActualTorusManifoldImmersion
import TwoAxisHelicoid.FlatCapOriginalManifold
import TwoAxisHelicoid.EquivariantTorusFrame
import TwoAxisHelicoid.SpatialGramFrames

namespace TwoAxisHelicoid
open Complex Filter Set Topology
open scoped ContDiff Manifold

variable (L : PeriodPair) (F : PeriodTorus L → Fin 3 → ℝ)

theorem lifted_fderiv_periodic (z v : ℂ) (hv : v ∈ L.lattice) :
    fderiv ℝ (F ∘ periodTorusProjection L) (z+v) = fderiv ℝ (F ∘ periodTorusProjection L) z := by
  let Y := F ∘ periodTorusProjection L
  have hp : (fun w => Y (w+v)) = Y := by
    funext w
    exact congrArg F (QuotientAddGroup.eq_iff_sub_mem.mpr (by simpa using hv))
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := Y) (x := z) v
  rw [hp] at h
  exact h.symm

theorem spatial_torus_lift_regular_at {z : ℂ} (hz : z ∉ L.lattice)
    (hsm : ∀ q ≠ 0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F q)
    (hi : ∀ q ≠ 0, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) F q)) :
    ContDiffAt ℝ ∞ (F ∘ periodTorusProjection L) z ∧
      Function.Injective (fderiv ℝ (F ∘ periodTorusProjection L) z) := by
  let q := periodTorusProjection L z
  let a := chartAt ℂ q q
  have hq : q ≠ 0 := fun he => hz ((periodTorusProjection_eq_zero L z).mp he)
  have hs := hsm q hq
  have hqa : periodTorusProjection L a = q := periodTorus_chart_representative L q
  have hω : a-z ∈ L.lattice := QuotientAddGroup.eq_iff_sub_mem.mp hqa
  let Y := F ∘ periodTorusProjection L
  have ha : ContDiffAt ℝ ∞ Y a := by
    have hchart : ContDiffAt ℝ ∞ (F ∘ (chartAt ℂ q).symm) a := by
      simpa only [mfld_simps,contDiffWithinAt_univ] using! (contMDiffAt_iff.mp hs).2
    rwa [periodTorus_chart_symm_eq_projection L q] at hchart
  have hei : Function.Injective (fderiv ℝ Y a) := by
    have h := hi q hq
    rw [manifold_to_normed_chart_derivative hs,periodTorus_chart_symm_eq_projection L q] at h
    exact h
  have haz : z+(a-z) = a := by abel
  have hper : (fun w => Y (w+(a-z))) = Y := by
    funext w
    exact congrArg F (QuotientAddGroup.eq_iff_sub_mem.mpr (by simpa using hω))
  have hc : ContDiffAt ℝ ∞ Y (z+(a-z)) := by rw [haz]; exact ha
  have hc' := hc.comp (f := fun w : ℂ => w+(a-z)) z (contDiffAt_id.add contDiffAt_const)
  have hd := lifted_fderiv_periodic L F z (a-z) hω
  rw [haz] at hd
  refine ⟨?_,hd ▸ hei⟩
  change ContDiffAt ℝ ∞ ((fun w => Y (w+(a-z)))) z at hc'
  rwa [hper] at hc'

variable (hsm : ∀ q ≠ 0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F q)
    (hi : ∀ q ≠ 0, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) F q))

noncomputable def puncturedPlaneGramFrame (z : PuncturedLatticePlane L) : OrthonormalTangentPair :=
  spatialDifferentialFrame (spatial_torus_lift_regular_at L F z.2 hsm hi).2 (v := 1) one_ne_zero

theorem puncturedPlaneGramFrame_same_fiber (z w : PuncturedLatticePlane L) (h : puncturedPlaneProjection L z = puncturedPlaneProjection L w) :
    puncturedPlaneGramFrame L F hsm hi z = puncturedPlaneGramFrame L F hsm hi w := by
  have hv := (puncturedPlaneProjection_eq_iff L z w).mp h
  have hd := lifted_fderiv_periodic L F w.1 (z.1-w.1) hv
  rw [show w.1+(z.1-w.1)=z.1 by abel] at hd
  apply Subtype.ext
  change spatialGramFrame _ _ = spatialGramFrame _ _
  rw [hd]

theorem puncturedPlaneGramFrame_continuous : Continuous (puncturedPlaneGramFrame L F hsm hi) := by
  have hD : Continuous (fun z : PuncturedLatticePlane L => fderiv ℝ (F ∘ periodTorusProjection L) z.1) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact ((spatial_torus_lift_regular_at L F z.2 hsm hi).1.continuousAt_fderiv (by simp)).comp
      (f := (Subtype.val : PuncturedLatticePlane L → ℂ)) continuous_subtype_val.continuousAt
  exact spatialDifferentialFrame_continuous hD continuous_const _ _

/-- The actual Euclidean Gram--Schmidt frame of any smooth regular marked
punctured torus, globally defined by descending the differentiated map. -/
noncomputable def puncturedMarkedTangentFrame : C(PuncturedPeriodTorus L,OrthonormalTangentPair) :=
  ⟨quotientFiberDescend _ (puncturedPlaneProjection_surjective L) (puncturedPlaneGramFrame L F hsm hi),
    quotientFiberDescend_continuous (puncturedPlaneProjection_isQuotientMap L) _
      (puncturedPlaneGramFrame_same_fiber L F hsm hi) (puncturedPlaneGramFrame_continuous L F hsm hi)⟩

theorem puncturedMarkedTangentFrame_projection (z : PuncturedLatticePlane L) :
    puncturedMarkedTangentFrame L F hsm hi (puncturedPlaneProjection L z) =
      puncturedPlaneGramFrame L F hsm hi z :=
  quotientFiberDescend_apply _ _ _ (puncturedPlaneGramFrame_same_fiber L F hsm hi) z

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.puncturedMarkedTangentFrame_projection
