import TwoAxisHelicoid.StandardSolidTorusRegular
import TwoAxisHelicoid.SolidTorusMeridianDisk
import TwoAxisHelicoid.PuncturedCompressingDiskParity

namespace TwoAxisHelicoid
open Complex Set Topology Metric
open scoped ContDiff Manifold

noncomputable def standardRoundTorusParameter (v : Circle × Circle) : Fin 3 → ℝ :=
  standardSolidToroidalPoint v.1 v.2

/-- The standard round torus has even actual ambient spin in every
marking that is regular on the puncture complement, with no assumption
about the marked homology classes chosen by a parametrization. -/
theorem standard_round_torus_all_markings_even (L : PeriodPair) {F : PeriodTorus L → Fin 3 → ℝ}
    (hF : IsEmbedding F) (hrange : range standardRoundTorusParameter = range F)
    (hs : ∀ q ≠ 0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F q)
    (hi : ∀ q ≠ 0, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) F q)) :
    capAmbientSpinQuadratic L F (1,0) * capAmbientSpinQuadratic L F (0,1) = 0 := by
  let b (v : Circle × Circle) := (v.1,(v.2:ℂ))
  have hbc : Continuous b := continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hbi : Function.Injective b := fun x y h => Prod.ext (congrArg (Prod.fst : Circle × ℂ → Circle) h)
    (Subtype.ext (congrArg (Prod.snd : Circle × ℂ → ℂ) h))
  have hm (v : Circle × Circle) : b v ∈ univ ×ˢ closedBall (0:ℂ) 1 := ⟨trivial,by simp [b,mem_closedBall]⟩
  have hei : Function.Injective standardRoundTorusParameter := fun x y h =>
    hbi (standardSolidToroidalPoint_injective_on (hm x) (hm y) h)
  have hec : Continuous standardRoundTorusParameter := standardSolidToroidalPoint_continuous.comp hbc
  obtain ⟨H,hH⟩ := same_range_parameter_homeomorph (hec.isClosedEmbedding hei).isEmbedding hF hrange
  obtain ⟨a,ha,_⟩ := solid_torus_has_meridian_avoiding_finite id Function.injective_id (∅ : Set (Circle × MeridianDiskParameter))
    finite_empty {(H.symm 0).1} (finite_singleton _)
  have h0 (u : Circle) : H (a,u) ≠ 0 := by
    intro hz
    apply ha
    exact congrArg Prod.fst ((H.symm_apply_apply (a,u)).symm.trans (congrArg H.symm hz))
  let A := unitVerticalRotation (a:ℂ) a.norm_coe
  let E : ℝ × ℂ → Fin 3 → ℝ := A ∘ standardMeridianChart
  have hE : ContDiff ℝ ∞ E := A.contDiff.comp standardMeridianChart_contDiff
  have hEi (z : ℂ) (hz : z ∈ closedBall (0:ℂ) 1) : Function.Injective (fderiv ℝ E (0,z)) := by
    have hd := (A.hasFDerivAt).comp (0,z) (standardMeridianChart_contDiff.differentiable (by simp) (0,z)).hasFDerivAt
    rw [show fderiv ℝ E (0,z) = _ from hd.fderiv]
    exact A.injective.comp (standardMeridianChart_fderiv_injective hz)
  have hb (s : ℝ) (u : Circle) : F (H (Circle.exp s*a,u)) = E (s,(u:ℂ)) :=
    (hH _).trans (standardToroid_longitude_formula a (s,(u:ℂ)))
  obtain ⟨ξ,period,hξ,hx,hω,hωL,hper,hr,hsi,hG,hGD,hGi,hbd,htr⟩ :=
    solid_torus_meridian_disk_data L hs hi H a h0 E (fun _ _ => hE.contDiffAt)
      hEi (δ := 1) zero_lt_one (fun s _ u => hb s u)
  exact punctured_marked_torus_with_compressing_disk_even L hs hi hξ hx hω hωL hper hr hsi hG hGD hGi hbd htr

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.standard_round_torus_all_markings_even
