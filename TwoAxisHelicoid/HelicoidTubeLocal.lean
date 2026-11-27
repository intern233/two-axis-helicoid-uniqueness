import TwoAxisHelicoid.HelicoidTubeInjective
import TwoAxisHelicoid.PlanarLocalInverse
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

namespace TwoAxisHelicoid
open Real Set

abbrev HelicoidTubeCoordinates := (ℝ × ℝ) × ℝ

noncomputable def helicoidTubeShear : HelicoidTubeCoordinates ≃ₜ HelicoidTubeCoordinates where
  toFun := fun p => (p.1,p.2+helicoidAngle p.1.2 p.1.1)
  invFun := fun p => (p.1,p.2-helicoidAngle p.1.2 p.1.1)
  left_inv := by intro p; simp
  right_inv := by intro p; simp
  continuous_toFun := continuous_fst.prodMk
    (continuous_snd.add (helicoidAngle_continuous.comp continuous_fst))
  continuous_invFun := continuous_fst.prodMk
    (continuous_snd.sub (helicoidAngle_continuous.comp continuous_fst))

noncomputable def helicoidTubeRotation : HelicoidTubeCoordinates ≃ₜ HelicoidTubeCoordinates where
  toFun := fun p => ((p.1.1*cos p.2-p.1.2*sin p.2,p.1.1*sin p.2+p.1.2*cos p.2),p.2)
  invFun := fun p => ((p.1.1*cos p.2+p.1.2*sin p.2,-p.1.1*sin p.2+p.1.2*cos p.2),p.2)
  left_inv := by
    intro p
    apply Prod.ext
    · apply Prod.ext <;> dsimp <;>
        nlinarith [congrArg (fun x : ℝ => p.1.1*x) (sin_sq_add_cos_sq p.2),
          congrArg (fun x : ℝ => p.1.2*x) (sin_sq_add_cos_sq p.2)]
    · rfl
  right_inv := by
    intro p
    apply Prod.ext
    · apply Prod.ext <;> dsimp <;>
        nlinarith [congrArg (fun x : ℝ => p.1.1*x) (sin_sq_add_cos_sq p.2),
          congrArg (fun x : ℝ => p.1.2*x) (sin_sq_add_cos_sq p.2)]
    · rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

noncomputable def helicoidTubeMap (p : HelicoidTubeCoordinates) : HelicoidTubeCoordinates :=
  let v := helicoidNormalMap p.1.2 p.2 p.1.1
  ((v.1,v.2.1),v.2.2)

theorem helicoidTubeMap_reduced (p : HelicoidTubeCoordinates) :
    helicoidTubeRotation.symm (helicoidTubeMap p) =
      ((helicoidU p.1.2 p.1.1,helicoidV p.1.2 p.1.1),(helicoidTubeShear p).2) := by
  apply Prod.ext
  · exact helicoidNormalMap_reduce p.1.2 p.2 p.1.1
  · rfl

theorem helicoidTubeMap_factor (p : HelicoidTubeCoordinates) :
    helicoidTubeMap p = helicoidTubeRotation
      ((helicoidU p.1.2 p.1.1,helicoidV p.1.2 p.1.1),(helicoidTubeShear p).2) := by
  rw [← helicoidTubeMap_reduced,Homeomorph.apply_symm_apply]

/-- The explicit width-one normal map is locally invertible everywhere in its
strip. The local inverse has an open domain and is continuous. -/
theorem helicoidTubeMap_local_homeomorph {p : HelicoidTubeCoordinates} (hs : |p.1.1| < 1) :
    ∃ e : OpenPartialHomeomorph HelicoidTubeCoordinates HelicoidTubeCoordinates,
      p ∈ e.source ∧ (e : HelicoidTubeCoordinates → HelicoidTubeCoordinates) = helicoidTubeMap := by
  have hdet : helicoidUs p.1.2 p.1.1*helicoidVr p.1.2 p.1.1-
      helicoidUr p.1.2 p.1.1*helicoidVs p.1.2 p.1.1 ≠ 0 := by
    have hj := helicoid_jacobian_neg p.1.2 p.1.1 hs
    linarith
  obtain ⟨e,he,heq,_⟩ := planar_local_inverse
    (fun s r => helicoidU_s_hasDerivAt r s) (fun s r => helicoidU_r_hasDerivAt r s)
    (fun s r => helicoidV_s_hasDerivAt r s) (fun s r => helicoidV_r_hasDerivAt r s)
    helicoidUs_continuous helicoidUr_continuous helicoidVs_continuous helicoidVr_continuous hdet
  let E := (helicoidTubeShear.toOpenPartialHomeomorph.trans
    (e.prod (OpenPartialHomeomorph.refl ℝ))).transHomeomorph helicoidTubeRotation
  refine ⟨E,?_,?_⟩
  · change p ∈ Set.univ ∩ helicoidTubeShear ⁻¹' (e.source ×ˢ Set.univ)
    exact ⟨mem_univ _,he,mem_univ _⟩
  · funext q
    change helicoidTubeRotation (e (helicoidTubeShear q).1,(helicoidTubeShear q).2) = helicoidTubeMap q
    rw [heq]
    exact (helicoidTubeMap_factor q).symm

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoidTubeMap_local_homeomorph
