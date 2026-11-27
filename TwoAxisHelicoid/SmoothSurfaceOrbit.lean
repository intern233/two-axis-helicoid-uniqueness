import TwoAxisHelicoid.RegularAnalyticSurfaceLift
import TwoAxisHelicoid.BoundedSmoothODE

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff NNReal

/-- A regular twice differentiable surface chart has a twice differentiable
left inverse on its local sheet. -/
theorem regular_smooth_surface_local_inverse {Y : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hY : ContDiffAt ℝ 2 Y z) (hi : Function.Injective (fderiv ℝ Y z)) :
    ∃ τ : (Fin 3 → ℝ) → ℂ, ContDiffAt ℝ 2 τ (Y z) ∧
      ∀ᶠ w in 𝓝 z, τ (Y w) = w := by
  obtain ⟨i,j,_,hm⟩ := regular_immersion_coordinate_minor _ hi
  let P := spatialGraphProjection i j
  let f := P ∘ Y
  let D := P.comp (fderiv ℝ Y z)
  have hf : ContDiffAt ℝ 2 f z := P.contDiff.contDiffAt.comp z hY
  have hD : HasFDerivAt f D z := P.hasFDerivAt.comp z (hY.differentiableAt (by norm_num)).hasFDerivAt
  have hinj : Function.Injective D := spatialGraphProjection_injective _ _ _ hm
  let D' := (LinearEquiv.ofBijective D.toLinearMap ⟨hinj,LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv
  have hD' : HasFDerivAt f (D' : ℂ →L[ℝ] ℂ) z := hD
  let e := hf.toOpenPartialHomeomorph f hD' (by simp)
  have he : z ∈ e.source := hf.mem_toOpenPartialHomeomorph_source hD' (by simp)
  have hInv : ContDiffAt ℝ 2 e.symm (f z) := hf.to_localInverse hD' (by norm_num)
  have hInv' : ContDiffAt ℝ 2 e.symm (P (Y z)) := hInv
  refine ⟨e.symm ∘ P,hInv'.comp _ P.contDiff.contDiffAt,?_⟩
  filter_upwards [e.open_source.mem_nhds he] with w hw
  exact e.left_inv hw

/-- An ambient integral curve of a tangent field stays on a regular smooth
sheet for a neighborhood of the initial time. Only local Lipschitz bounds
are used. -/
theorem smooth_tangent_orbit_local {S : Set (Fin 3 → ℝ)} {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hX : ContDiffAt ℝ 2 X z) (hi : Function.Injective (fderiv ℝ X z))
    {V : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hV : ContDiffAt ℝ 1 V (X z))
    (ht : ∀ᶠ w in 𝓝 z, X w ∈ S ∧ ∃ v, fderiv ℝ X w v = V (X w))
    {γ : ℝ → Fin 3 → ℝ} {s : ℝ}
    (hγ : ∀ᶠ t in 𝓝 s, HasDerivAt γ (V (γ t)) t) (hs : γ s = X z) :
    ∀ᶠ t in 𝓝 s, γ t ∈ S := by
  obtain ⟨τ,hτ,hleft⟩ := regular_smooth_surface_local_inverse hX hi
  let F := fun w => fderiv ℝ τ (X w) (V (X w))
  have hX₁ : ContDiffAt ℝ 1 X z := hX.of_le (by norm_num)
  have hF : ContDiffAt ℝ 1 F z :=
    ((hτ.fderiv_right (by norm_num)).comp z hX₁).clm_apply (hV.comp z hX₁)
  obtain ⟨u,hu,ε,hε,hd⟩ := hF.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ s
  have hint : Ioo (s-ε) (s+ε) ∈ 𝓝 s := Ioo_mem_nhds (by linarith) (by linarith)
  have hcont : Tendsto u (𝓝 s) (𝓝 z) := hu ▸ (hd s (mem_of_mem_nhds hint)).continuousAt
  have hx := hX₁.eventually (by simp)
  have hτ₁ : ContDiffAt ℝ 1 τ (X z) := hτ.of_le (by norm_num)
  have hinv : ∀ᶠ w in 𝓝 z, fderiv ℝ X w (F w) = V (X w) := by
    filter_upwards [ht,hx,hX.continuousAt.eventually (hτ₁.eventually (by simp)),
      eventually_eventually_nhds.mpr hleft] with w hw hxw hτw hwleft
    obtain ⟨v,hv⟩ := hw.2
    have left : τ ∘ X =ᶠ[𝓝 w] id := hwleft
    have he := (hτw.differentiableAt_one.hasFDerivAt.comp w hxw.differentiableAt_one.hasFDerivAt).congr_of_eventuallyEq left.symm
    have h := congrArg (fun D : ℂ →L[ℝ] ℂ => D v) (he.unique (hasFDerivAt_id w))
    change fderiv ℝ τ (X w) (fderiv ℝ X w v) = v at h
    unfold F
    rw [← hv,h]
  obtain ⟨K,B,hB,hl⟩ := hV.exists_lipschitzOnWith
  have hγB := (hs ▸ hγ.self_of_nhds.continuousAt : Tendsto γ (𝓝 s) (𝓝 (X z))).eventually hB
  have huB := (hX.continuousAt.tendsto.comp hcont).eventually hB
  have huODE : ∀ᶠ t in 𝓝 s, HasDerivAt (X ∘ u) (V ((X ∘ u) t)) t := by
    filter_upwards [hint,hcont.eventually hinv,hcont.eventually hx] with t hti he hxw
    exact he ▸ hxw.differentiableAt_one.hasFDerivAt.comp_hasDerivAt t (hd t hti)
  have eq := ODE_solution_unique_of_eventually (s := fun _ : ℝ => B) (v := fun _ => V)
    (Eventually.of_forall fun _ => hl) (huODE.and huB) (hγ.and hγB)
    (show (X ∘ u) s = γ s by rw [Function.comp_apply,hu,hs])
  filter_upwards [eq,hcont.eventually ht] with t he ht'
  exact he ▸ ht'.1

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_tangent_orbit_local
