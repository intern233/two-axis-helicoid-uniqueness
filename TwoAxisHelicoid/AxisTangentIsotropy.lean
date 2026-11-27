import TwoAxisHelicoid.RegularAnalyticSurfaceLift
import TwoAxisHelicoid.SurfaceDotLaplacian
import TwoAxisHelicoid.ImmersedSimilarityRigidity

namespace TwoAxisHelicoid
open Complex Set Filter Topology Matrix
open scoped Topology

/-- A differentiable spatial curve in an embedded surface has velocity
in the actual parametrized tangent plane. Only continuity of the
topological lift is needed before taking the chart's smooth left inverse. -/
theorem embedded_chart_contains_curve_velocity {M : Type*} [TopologicalSpace M]
    (Y : M → Fin 3 → ℝ) (hy : IsEmbedding Y) (e : OpenPartialHomeomorph M ℂ) {p : M} (hp : p ∈ e.source)
    (hx : AnalyticAt ℝ (Y ∘ e.symm) (e p)) (hi : Function.Injective (fderiv ℝ (Y ∘ e.symm) (e p)))
    {γ : ℝ → Fin 3 → ℝ} {s : ℝ} {v : Fin 3 → ℝ} (hγ : HasDerivAt γ v s)
    (atp : γ s=Y p) (inside : ∀ᶠ t in 𝓝 s, γ t ∈ range Y) :
    ∃ w : ℂ, fderiv ℝ (Y ∘ e.symm) (e p) w=v := by
  let X := Y ∘ e.symm
  have xp : X (e p)=Y p := congrArg Y (e.left_inv hp)
  obtain ⟨τ,atτ,left⟩ := regular_analytic_surface_local_inverse hx hi
  have center : τ (γ s)=e p := by rw [atp,← xp]; exact left.self_of_nhds
  have aτ : DifferentiableAt ℝ τ (γ s) := by
    rw [atp,← xp]
    exact atτ.differentiableAt
  have good : ∀ᶠ q in 𝓝 p, X (τ (Y q))=Y q := by
    filter_upwards [e.open_source.mem_nhds hp,(e.continuousAt hp).eventually left] with q hq h
    have val : X (e q)=Y q := congrArg Y (e.left_inv hq)
    rw [← val,h]
  have onImage : ∀ᶠ y in 𝓝[range Y] (Y p), X (τ y)=y := by
    rw [← hy.map_nhds_eq p]; exact good
  have tend : Tendsto γ (𝓝 s) (𝓝[range Y] (Y p)) :=
    tendsto_nhdsWithin_iff.mpr ⟨atp ▸ hγ.continuousAt.tendsto,inside⟩
  have eq : X ∘ (τ ∘ γ) =ᶠ[𝓝 s] γ := tend.eventually onImage
  have d := aτ.hasFDerivAt.comp_hasDerivAt s hγ
  have ax : DifferentiableAt ℝ X (τ (γ s)) := center.symm ▸ hx.differentiableAt
  have composed := ax.hasFDerivAt.comp_hasDerivAt s d
  exact ⟨_,center ▸ (composed.congr_of_eventuallyEq eq.symm).unique hγ⟩

/-- An infinitesimal vertical rotation fixing a point cannot preserve
a tangent plane containing the vertical axis unless the rotation
velocity is zero. The conclusion is obtained from the derivative of
the vanishing normal component in the given surface chart. -/
theorem vertical_rotation_zero_at_tangent_fixed_point {X N : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hx : DifferentiableAt ℝ X z) (hn : DifferentiableAt ℝ N z) (hi : Function.Injective (fderiv ℝ X z))
    (unit : N z ⬝ᵥ N z=1) (normal : ∀ w, fderiv ℝ X z w ⬝ᵥ N z=0)
    (axis : ∃ w : ℂ, fderiv ℝ X z w=![0,0,1]) (a b : Fin 3 → ℝ) (d : ℝ) (b0 : b 0=0) (b1 : b 1=0)
    (fixed : similarityField a b d (X z)=0) (tangent : ∀ᶠ w in 𝓝 z, similarityField a b d (X w) ⬝ᵥ N w=0) :
    b 2=0 := by
  let D := fderiv ℝ X z
  let n := N z
  let L := similarityLinear b d
  let V := fun w => similarityField a b d (X w)
  have dV : HasFDerivAt V (L.comp D) z := by
    simpa only [V,L,similarityField,similarityLinear_apply,Function.comp_apply,add_assoc] using!
      (L.hasFDerivAt.comp z hx.hasFDerivAt).const_add a
  obtain ⟨u,hu⟩ := axis
  have n2 : n 2=0 := by
    have e := normal u
    rw [hu] at e
    simpa [n,dotProduct,Fin.sum_univ_succ] using e
  have ns : n 0*n 0+n 1*n 1=1 := by
    simpa [dotProduct,Fin.sum_univ_succ,n2,add_assoc] using (show n ⬝ᵥ n=1 from unit)
  by_contra bn
  have vertical (v : ℂ) : D v 0=0 ∧ D v 1=0 := by
    have der := derivative_of_constant_pairing dV.differentiableAt hn (c := 0) tangent v
    change V z ⬝ᵥ _+fderiv ℝ V z v ⬝ᵥ n=0 at der
    rw [show V z=0 from fixed,zero_dotProduct,zero_add,dV.fderiv] at der
    change (b ⨯₃ D v+d • D v) ⬝ᵥ n=0 at der
    rw [add_dotProduct,smul_dotProduct,show D v ⬝ᵥ n=0 from normal v,smul_zero,add_zero] at der
    have e : D v 0*n 0+D v 1*n 1=0 := by
      simpa [dotProduct,Fin.sum_univ_succ,n2,add_assoc] using (show D v ⬝ᵥ n=0 from normal v)
    have ec : b 2*(D v 0*n 1-D v 1*n 0)=0 := by
      exact (show b 2*(D v 0*n 1-D v 1*n 0)=(b ⨯₃ D v) ⬝ᵥ n by simp [cross_apply,dotProduct,Fin.sum_univ_succ,b0,b1]; ring).trans der
    have cross := (mul_eq_zero.mp ec).resolve_left bn
    constructor
    · linear_combination n 0*e+n 1*cross-(D v 0)*ns
    · linear_combination n 1*e-n 0*cross-(D v 1)*ns
  have dep : D ((D I 2) • (1:ℂ))=D ((D 1 2) • I) := by
    rw [map_smul,map_smul]
    funext j
    fin_cases j <;> simp [vertical,smul_eq_mul,mul_comm]
  have h := congrArg Complex.im (hi dep)
  have h2 : D 1 2=0 := by simpa [Complex.real_smul] using h.symm
  have zero : D 1=0 := by funext j; fin_cases j <;> simp [vertical,h2]
  exact one_ne_zero (hi (zero.trans D.map_zero.symm))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.embedded_chart_contains_curve_velocity
#print axioms TwoAxisHelicoid.vertical_rotation_zero_at_tangent_fixed_point
