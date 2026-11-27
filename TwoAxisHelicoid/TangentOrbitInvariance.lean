import TwoAxisHelicoid.RegularAnalyticSurfaceLift
import Mathlib.Analysis.ODE.ExistUnique

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology NNReal

/-- A locally tangent analytic vector field lifts to an actual parameter ODE
on each regular chart. Its spatial integral curve agrees with the ambient
orbit by local uniqueness. -/
theorem tangent_ambient_orbit_locally_in_image {X : ℂ → Fin 3 → ℝ} {U : Set ℂ}
    (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) (hX : AnalyticAt ℝ X z)
    (hi : Function.Injective (fderiv ℝ X z))
    {V : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hV : AnalyticAt ℝ V (X z))
    {K : ℝ≥0} (hlip : LipschitzWith K V)
    (ht : ∀ w ∈ U, ∃ v : ℂ, fderiv ℝ X w v = V (X w))
    {γ : ℝ → Fin 3 → ℝ} {s : ℝ} (hγ : ∀ t, HasDerivAt γ (V (γ t)) t)
    (hs : γ s = X z) : ∀ᶠ t in 𝓝 s, γ t ∈ X '' U := by
  obtain ⟨τ,hτ,hleft⟩ := regular_analytic_surface_local_inverse hX hi
  let F := fun w => fderiv ℝ τ (X w) (V (X w))
  have hF : AnalyticAt ℝ F z := ((ContinuousLinearMap.apply ℝ ℂ (E' := Fin 3 → ℝ)).flip.analyticAt_bilinear _).comp₂ (hτ.fderiv.comp hX) (hV.comp hX)
  obtain ⟨u,hu,ε,hε,hode⟩ := (hF.contDiffAt : ContDiffAt ℝ 1 F z)
    |>.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ s
  have hint : Set.Ioo (s-ε) (s+ε) ∈ 𝓝 s := Ioo_mem_nhds (by linarith) (by linarith)
  have hu' : Tendsto u (𝓝 s) (𝓝 z) := hu ▸ (hode s ((mem_of_mem_nhds hint))).continuousAt
  have hinv : ∀ᶠ w in 𝓝 z, fderiv ℝ X w (F w) = V (X w) := by
    filter_upwards [hU.mem_nhds hz,hX.eventually_analyticAt,hX.continuousAt.eventually hτ.eventually_analyticAt,
      eventually_eventually_nhds.mpr hleft] with w hw hx hτw hwleft
    obtain ⟨v,hv⟩ := ht w hw
    have he : τ ∘ X =ᶠ[𝓝 w] id := hwleft
    have hd := (hτw.differentiableAt.hasFDerivAt.comp w hx.differentiableAt.hasFDerivAt).congr_of_eventuallyEq he.symm
    have hh := congrArg (fun D : ℂ →L[ℝ] ℂ => D v) (hd.unique (hasFDerivAt_id w))
    change fderiv ℝ τ (X w) (fderiv ℝ X w v) = v at hh
    unfold F
    rw [← hv,hh]
  have hs' : ∀ᶠ t in 𝓝 s, HasDerivAt (X ∘ u) (V ((X ∘ u) t)) t := by
    filter_upwards [hint,hu'.eventually hinv,hu'.eventually hX.eventually_analyticAt] with t hti he hx
    exact he ▸ hx.differentiableAt.hasFDerivAt.comp_hasDerivAt t (hode t hti)
  have he := ODE_solution_unique_of_eventually (s := fun _ : ℝ => (univ : Set (Fin 3 → ℝ)))
    (v := fun _ => V) (t₀ := s) (Eventually.of_forall fun _ => hlip.lipschitzOnWith)
    (hs'.mono fun _ h => ⟨h,mem_univ _⟩) (Eventually.of_forall fun t => ⟨hγ t,mem_univ _⟩)
    (show (X ∘ u) s = γ s by rw [Function.comp_apply,hu,hs])
  filter_upwards [he,hu'.eventually (hU.mem_nhds hz)] with t h ht'
  exact ⟨u t,ht',h⟩

/-- Proper embeddedness supplies closedness of the full spatial image.
Local integral curves and connectedness of time give invariance for every
finite time along the ambient flow. -/
theorem tangent_ambient_orbit_in_closed_image {X : ℂ → Fin 3 → ℝ} {U : Set ℂ}
    (hU : IsOpen U) (hclosed : IsClosed (X '' U))
    (hX : ∀ z ∈ U, AnalyticAt ℝ X z ∧ Function.Injective (fderiv ℝ X z))
    {V : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hV : ∀ p, AnalyticAt ℝ V p)
    {K : ℝ≥0} (hlip : LipschitzWith K V)
    (ht : ∀ w ∈ U, ∃ v : ℂ, fderiv ℝ X w v = V (X w))
    {γ : ℝ → Fin 3 → ℝ} (hγ : ∀ t, HasDerivAt γ (V (γ t)) t)
    {s : ℝ} (hs : γ s ∈ X '' U) (t : ℝ) : γ t ∈ X '' U := by
  let A := γ ⁻¹' (X '' U)
  have hA : IsClosed A := hclosed.preimage (continuous_iff_continuousAt.mpr fun r => (hγ r).continuousAt)
  have ho : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    rintro r ⟨z,hz,hr⟩
    exact tangent_ambient_orbit_locally_in_image hU hz (hX z hz).1 (hX z hz).2 (hV _) hlip ht hγ hr.symm
  have hwhole := IsClopen.eq_univ ⟨hA,ho⟩ (show A.Nonempty from ⟨s,hs⟩)
  exact (show t ∈ A by rw [hwhole]; exact mem_univ _)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.tangent_ambient_orbit_in_closed_image
