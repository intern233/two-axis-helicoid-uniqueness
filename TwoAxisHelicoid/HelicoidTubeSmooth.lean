import TwoAxisHelicoid.HelicoidTubeLocal
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

namespace TwoAxisHelicoid
open Real Set
open scoped ContDiff

theorem helicoid_reduced_contDiff : ContDiff ℝ (∞ : WithTop ℕ∞)
    (fun p : ℝ × ℝ => (helicoidU p.2 p.1,helicoidV p.2 p.1)) := by
  unfold helicoidU helicoidV helicoidAngle helicoidQ
  fun_prop (disch := intros; positivity)

theorem helicoidTubeShear_symm_contDiff : ContDiff ℝ (∞ : WithTop ℕ∞)
    helicoidTubeShear.symm := by
  change ContDiff ℝ (∞ : WithTop ℕ∞)
    (fun p : HelicoidTubeCoordinates => (p.1,p.2-helicoidAngle p.1.2 p.1.1))
  unfold helicoidAngle helicoidQ
  fun_prop (disch := intros; positivity)

theorem helicoidTubeRotation_symm_contDiff : ContDiff ℝ (∞ : WithTop ℕ∞)
    helicoidTubeRotation.symm := by
  change ContDiff ℝ (∞ : WithTop ℕ∞) (fun p : HelicoidTubeCoordinates =>
    ((p.1.1*cos p.2+p.1.2*sin p.2,-p.1.1*sin p.2+p.1.2*cos p.2),p.2))
  fun_prop

theorem helicoidTubeMap_contDiff : ContDiff ℝ (∞ : WithTop ℕ∞) helicoidTubeMap := by
  unfold helicoidTubeMap helicoidNormalMap helicoidAngle helicoidQ
  fun_prop (disch := intros; positivity)

theorem helicoid_reduced_local_smooth_inverse {p : ℝ × ℝ} (hs : |p.1| < 1) :
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      p ∈ e.source ∧ (e : (ℝ × ℝ) → ℝ × ℝ) =
        (fun q => (helicoidU q.2 q.1,helicoidV q.2 q.1)) ∧
      ContDiffAt ℝ (∞ : WithTop ℕ∞) e.symm (helicoidU p.2 p.1,helicoidV p.2 p.1) := by
  have hdet : helicoidUs p.2 p.1*helicoidVr p.2 p.1-
      helicoidUr p.2 p.1*helicoidVs p.2 p.1 ≠ 0 := by
    have hj := helicoid_jacobian_neg p.2 p.1 hs
    linarith
  obtain ⟨e,he,heq,_⟩ := planar_local_inverse
    (fun s r => helicoidU_s_hasDerivAt r s) (fun s r => helicoidU_r_hasDerivAt r s)
    (fun s r => helicoidV_s_hasDerivAt r s) (fun s r => helicoidV_r_hasDerivAt r s)
    helicoidUs_continuous helicoidUr_continuous helicoidVs_continuous helicoidVr_continuous hdet
  let D := planarLinearEquiv (helicoidUs p.2 p.1) (helicoidUr p.2 p.1)
    (helicoidVs p.2 p.1) (helicoidVr p.2 p.1) hdet
  have hd : HasFDerivAt (fun q : ℝ × ℝ => (helicoidU q.2 q.1,helicoidV q.2 q.1))
      (D : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p :=
    ((scalar_bivariate_hasStrictFDerivAt
      (fun s r => helicoidU_s_hasDerivAt r s) (fun s r => helicoidU_r_hasDerivAt r s)
      helicoidUs_continuous helicoidUr_continuous).prodMk
      (scalar_bivariate_hasStrictFDerivAt
      (fun s r => helicoidV_s_hasDerivAt r s) (fun s r => helicoidV_r_hasDerivAt r s)
      helicoidVs_continuous helicoidVr_continuous)).hasFDerivAt
  refine ⟨e,he,heq,?_⟩
  have hep : e p = (helicoidU p.2 p.1,helicoidV p.2 p.1) := congrFun heq p
  have hback : e.symm (helicoidU p.2 p.1,helicoidV p.2 p.1) = p := by
    rw [← hep]
    exact e.left_inv he
  apply e.contDiffAt_symm (f₀' := D)
  · rw [← hep]
    exact e.map_source he
  · rw [hback,heq]
    exact hd
  · rw [hback,heq]
    exact helicoid_reduced_contDiff.contDiffAt

/-- The width-one normal map has a smooth local inverse at every point of
the strip, proving the local diffeomorphism assertion in PDF §4.2. -/
theorem helicoidTubeMap_local_diffeomorph {p : HelicoidTubeCoordinates} (hs : |p.1.1| < 1) :
    ∃ e : OpenPartialHomeomorph HelicoidTubeCoordinates HelicoidTubeCoordinates,
      p ∈ e.source ∧ (e : HelicoidTubeCoordinates → HelicoidTubeCoordinates) = helicoidTubeMap ∧
      ContDiffAt ℝ (∞ : WithTop ℕ∞) e.symm (helicoidTubeMap p) := by
  obtain ⟨e,he,heq,heinv⟩ := helicoid_reduced_local_smooth_inverse hs
  let E := (helicoidTubeShear.toOpenPartialHomeomorph.trans
    (e.prod (OpenPartialHomeomorph.refl ℝ))).transHomeomorph helicoidTubeRotation
  refine ⟨E,?_,?_,?_⟩
  · change p ∈ Set.univ ∩ helicoidTubeShear ⁻¹' (e.source ×ˢ Set.univ)
    exact ⟨mem_univ _,he,mem_univ _⟩
  · funext q
    change helicoidTubeRotation (e (helicoidTubeShear q).1,(helicoidTubeShear q).2) = helicoidTubeMap q
    rw [heq]
    exact (helicoidTubeMap_factor q).symm
  · change ContDiffAt ℝ (∞ : WithTop ℕ∞)
      (fun q => helicoidTubeShear.symm
        (e.symm (helicoidTubeRotation.symm q).1,(helicoidTubeRotation.symm q).2)) (helicoidTubeMap p)
    have hi : ContDiffAt ℝ (∞ : WithTop ℕ∞) (Prod.map e.symm (id : ℝ → ℝ))
        (helicoidTubeRotation.symm (helicoidTubeMap p)) := by
      rw [helicoidTubeMap_reduced]
      exact heinv.prodMap contDiffAt_id
    exact helicoidTubeShear_symm_contDiff.contDiffAt.comp _
      (hi.comp _ helicoidTubeRotation_symm_contDiff.contDiffAt)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoidTubeMap_local_diffeomorph
