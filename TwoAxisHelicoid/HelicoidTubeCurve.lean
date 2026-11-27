import TwoAxisHelicoid.HelicoidGlobalTube
import TwoAxisHelicoid.HelicoidTubeMetric
import TwoAxisHelicoid.VectorBivariateDerivative

namespace TwoAxisHelicoid
open Real Set Filter
open scoped Topology ContDiff

def tubeCartesian (p : HelicoidTubeCoordinates) : Fin 3 → ℝ := ![p.1.1,p.1.2,p.2]

theorem tubeCartesian_hasDerivAt {x : ℝ → HelicoidTubeCoordinates}
    {v : HelicoidTubeCoordinates} {τ : ℝ} (hx : HasDerivAt x v τ) :
    HasDerivAt (fun t => tubeCartesian (x t)) (tubeCartesian v) τ := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hx.fst.fst
  · exact hx.fst.snd
  · exact hx.snd

theorem tubeCartesian_normalMap (p : HelicoidTubeCoordinates) :
    tubeCartesian (helicoidTubeMap p) =
      standardHelicoid p.1.2 p.2+p.1.1 • standardHelicoidNormal p.1.2 p.2 :=
  helicoidNormalMap_is_normal_displacement p.1.2 p.2 p.1.1

theorem standardHelicoidR_joint_continuous :
    Continuous (fun p : ℝ × ℝ => standardHelicoidR p.2) := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [standardHelicoidR] <;> fun_prop

theorem standardHelicoidTheta_joint_continuous :
    Continuous (fun p : ℝ × ℝ => standardHelicoidTheta p.1 p.2) := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [standardHelicoidTheta] <;> fun_prop

theorem standardHelicoidNormal_r_joint_continuous :
    Continuous (fun p : ℝ × ℝ => (1/(helicoidQ p.1)^3) • standardHelicoidTheta p.1 p.2) := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [standardHelicoidTheta,helicoidQ] <;>
    fun_prop (disch := intros; positivity)

theorem standardHelicoidNormal_theta_joint_continuous :
    Continuous (fun p : ℝ × ℝ => (1/helicoidQ p.1) • standardHelicoidR p.2) := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [standardHelicoidR,helicoidQ] <;>
    fun_prop (disch := intros; positivity)

theorem standardHelicoid_curve_hasDerivAt {r θ : ℝ → ℝ} {a b τ : ℝ}
    (hr : HasDerivAt r a τ) (hθ : HasDerivAt θ b τ) :
    HasDerivAt (fun t => standardHelicoid (r t) (θ t))
      (a • standardHelicoidR (θ τ)+b • standardHelicoidTheta (r τ) (θ τ)) τ :=
  vector_bivariate_curve_hasDerivAt (F := standardHelicoid)
    (Ft := fun _ θ => standardHelicoidR θ) (Fa := standardHelicoidTheta)
    (Filter.Eventually.of_forall (fun p => standardHelicoid_r_hasDerivAt p.1 p.2))
    (Filter.Eventually.of_forall (fun p => standardHelicoid_theta_hasDerivAt p.1 p.2))
    standardHelicoidR_joint_continuous.continuousAt
    standardHelicoidTheta_joint_continuous.continuousAt hr hθ

theorem standardHelicoidNormal_curve_hasDerivAt {r θ : ℝ → ℝ} {a b τ : ℝ}
    (hr : HasDerivAt r a τ) (hθ : HasDerivAt θ b τ) :
    HasDerivAt (fun t => standardHelicoidNormal (r t) (θ t))
      (fun i => a/(helicoidQ (r τ))^3*standardHelicoidTheta (r τ) (θ τ) i+
        b/helicoidQ (r τ)*standardHelicoidR (θ τ) i) τ := by
  have hd := vector_bivariate_curve_hasDerivAt (F := standardHelicoidNormal)
    (Ft := fun r θ => (1/(helicoidQ r)^3) • standardHelicoidTheta r θ)
    (Fa := fun r θ => (1/helicoidQ r) • standardHelicoidR θ)
    (Filter.Eventually.of_forall (fun p => standardHelicoidNormal_r_hasDerivAt p.1 p.2))
    (Filter.Eventually.of_forall (fun p => standardHelicoidNormal_theta_hasDerivAt p.1 p.2))
    standardHelicoidNormal_r_joint_continuous.continuousAt
    standardHelicoidNormal_theta_joint_continuous.continuousAt hr hθ
  convert hd using 1
  funext i
  dsimp
  ring

theorem helicoidTube_curve_hasDerivAt {r θ s : ℝ → ℝ} {a b c τ : ℝ}
    (hr : HasDerivAt r a τ) (hθ : HasDerivAt θ b τ) (hs : HasDerivAt s c τ) :
    HasDerivAt (fun t => tubeCartesian (helicoidTubeMap ((s t,r t),θ t)))
      (fun i => a*helicoidTubeR (r τ) (θ τ) (s τ) i+
        b*helicoidTubeTheta (r τ) (θ τ) (s τ) i+
        c*standardHelicoidNormal (r τ) (θ τ) i) τ := by
  have hd := (standardHelicoid_curve_hasDerivAt hr hθ).add
    (hs.smul (standardHelicoidNormal_curve_hasDerivAt hr hθ))
  convert hd using 1
  · funext t
    exact tubeCartesian_normalMap _
  · funext i
    dsimp [helicoidTubeR,helicoidTubeTheta]
    ring

noncomputable def helicoidNormalField (y : HelicoidTubeCoordinates) : Fin 3 → ℝ :=
  standardHelicoidNormal (helicoidTubeEquiv.symm y).1.2 (helicoidTubeEquiv.symm y).2

theorem helicoidNormalField_contDiffAt {y : HelicoidTubeCoordinates}
    (hy : y ∈ helicoidTubeEquiv.target) :
    ContDiffAt ℝ (∞ : WithTop ℕ∞) helicoidNormalField y := by
  have hn : ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun p : HelicoidTubeCoordinates => standardHelicoidNormal p.1.2 p.2) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [standardHelicoidNormal,helicoidQ] <;>
      fun_prop (disch := intros; positivity)
  exact hn.contDiffAt.comp y (helicoidTubeEquiv_inverse_contDiffAt hy)

theorem helicoidTube_vector_dot_normal (r θ s a b c : ℝ) :
    (∑ i, standardHelicoidNormal r θ i*
      (a*helicoidTubeR r θ s i+b*helicoidTubeTheta r θ s i+c*standardHelicoidNormal r θ i)) = c := by
  have he : (fun i => standardHelicoidNormal r θ i*
      (a*helicoidTubeR r θ s i+b*helicoidTubeTheta r θ s i+c*standardHelicoidNormal r θ i)) =
      fun i => (a+s*b/helicoidQ r)*(standardHelicoidR θ i*standardHelicoidNormal r θ i)+
        (b+s*a/(helicoidQ r)^3)*(standardHelicoidTheta r θ i*standardHelicoidNormal r θ i)+
        c*(standardHelicoidNormal r θ i)^2 := by
    funext i
    dsimp [helicoidTubeR,helicoidTubeTheta]
    ring
  simp_rw [congrFun he]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum]
  obtain ⟨hN,hR,hT⟩ := standardHelicoid_unit_normal r θ
  rw [hN,hR,hT]
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoidTube_curve_hasDerivAt
