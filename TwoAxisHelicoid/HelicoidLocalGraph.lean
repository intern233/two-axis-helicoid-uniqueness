import TwoAxisHelicoid.HelicoidProjection

namespace TwoAxisHelicoid
open Real Set
open scoped ContDiff Topology

/-- The normal projection of a smooth immersed surface is a local
diffeomorphism whenever its actual tangent plane has a strict angle bound.
This is the local graph step; global properness and sheet counting remain
separate geometric hypotheses. -/
theorem helicoid_surface_projection_local_diffeomorph
    {X : (ℝ × ℝ) → HelicoidTubeCoordinates} {p : ℝ × ℝ}
    (hX : ContDiffAt ℝ (∞ : WithTop ℕ∞) X p)
    (hy : X p ∈ helicoidTubeEquiv.target)
    (hD : Function.Injective (fderiv ℝ X p))
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ < 1)
    (hangle : ∀ u : ℝ × ℝ,
      (∑ i, helicoidNormalField (X p) i*tubeCartesian ((fderiv ℝ X p) u) i)^2 ≤
        κ^2*(∑ i, (tubeCartesian ((fderiv ℝ X p) u) i)^2)) :
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      p ∈ e.source ∧ (e : (ℝ × ℝ) → ℝ × ℝ) = (fun z => helicoidBaseCoordinates (X z)) ∧
      ContDiffAt ℝ (∞ : WithTop ℕ∞) e.symm (helicoidBaseCoordinates (X p)) := by
  let f : (ℝ × ℝ) → ℝ × ℝ := fun z => helicoidBaseCoordinates (X z)
  let L := (fderiv ℝ helicoidBaseCoordinates (X p)).comp (fderiv ℝ X p)
  have hL : Function.Injective L := helicoid_projection_derivative_injective hy hD hκ0 hκ hangle
  let E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
    (LinearEquiv.ofInjectiveEndo L.toLinearMap hL).toContinuousLinearEquiv
  have hf : ContDiffAt ℝ (∞ : WithTop ℕ∞) f p :=
    (helicoidBaseCoordinates_contDiffAt hy).comp p hX
  have hd : HasFDerivAt f (E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p :=
    ((helicoidBaseCoordinates_contDiffAt hy).differentiableAt (by simp)).hasFDerivAt.comp p
      (hX.differentiableAt (by simp)).hasFDerivAt
  let e := hf.toOpenPartialHomeomorph f hd (by simp)
  refine ⟨e,hf.mem_toOpenPartialHomeomorph_source hd (by simp),rfl,?_⟩
  exact hf.to_localInverse hd (by simp)

/-- The local inverse gives an actual height function and a normal-graph
identity on an open base disk, not merely injectivity of a formal matrix. -/
theorem helicoid_surface_local_normal_graph
    {X : (ℝ × ℝ) → HelicoidTubeCoordinates} {p : ℝ × ℝ}
    (hX : ContDiffAt ℝ (∞ : WithTop ℕ∞) X p)
    (hy : X p ∈ helicoidTubeEquiv.target)
    (hD : Function.Injective (fderiv ℝ X p))
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ < 1)
    (hangle : ∀ u : ℝ × ℝ,
      (∑ i, helicoidNormalField (X p) i*tubeCartesian ((fderiv ℝ X p) u) i)^2 ≤
        κ^2*(∑ i, (tubeCartesian ((fderiv ℝ X p) u) i)^2)) :
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ), ∃ s : (ℝ × ℝ) → ℝ,
      p ∈ e.source ∧ (e : (ℝ × ℝ) → ℝ × ℝ) = (fun z => helicoidBaseCoordinates (X z)) ∧
      ContDiffAt ℝ (∞ : WithTop ℕ∞) s (helicoidBaseCoordinates (X p)) ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ q ∈ Metric.ball (helicoidBaseCoordinates (X p)) ρ,
        q ∈ e.target ∧ X (e.symm q) = helicoidTubeMap ((s q,q.1),q.2) := by
  obtain ⟨e,hep,he,hi⟩ := helicoid_surface_projection_local_diffeomorph hX hy hD hκ0 hκ hangle
  let q₀ := helicoidBaseCoordinates (X p)
  have hep' : e p = q₀ := congrFun he p
  have hback : e.symm q₀ = p := by
    rw [← hep']
    exact e.left_inv hep
  let Y : (ℝ × ℝ) → HelicoidTubeCoordinates := fun q => X (e.symm q)
  have hY : ContDiffAt ℝ (∞ : WithTop ℕ∞) Y q₀ := by
    apply ContDiffAt.comp q₀ _ hi
    simpa only [hback] using hX
  have hY0 : Y q₀ = X p := by dsimp [Y]; rw [hback]
  let s : (ℝ × ℝ) → ℝ := fun q => helicoidSignedDistance (Y q)
  have hs : ContDiffAt ℝ (∞ : WithTop ℕ∞) s q₀ := by
    have hYs : Y q₀ ∈ helicoidTubeEquiv.target := by rwa [hY0]
    exact (helicoidSignedDistance_contDiffAt hYs).comp q₀ hY
  have htarget : e.target ∈ 𝓝 q₀ := e.open_target.mem_nhds (hep' ▸ e.map_source hep)
  have hYtarget : ∀ᶠ q in 𝓝 q₀, Y q ∈ helicoidTubeEquiv.target :=
    hY.continuousAt.eventually (helicoidTubeEquiv_target_isOpen.mem_nhds (hY0 ▸ hy))
  obtain ⟨ρ,hρ,hsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem htarget hYtarget)
  refine ⟨e,s,hep,he,hs,ρ,hρ,?_⟩
  intro q hq
  obtain ⟨hqT,hqY⟩ := hsub hq
  refine ⟨hqT,?_⟩
  have hbase : helicoidBaseCoordinates (Y q) = q := by
    change helicoidBaseCoordinates (X (e.symm q)) = q
    rw [← congrFun he (e.symm q)]
    exact e.right_inv hqT
  have hcoord : helicoidTubeEquiv.symm (Y q) = ((s q,q.1),q.2) := by
    have h₁ : (helicoidTubeEquiv.symm (Y q)).1.2 = q.1 :=
      congrArg (fun r : ℝ × ℝ => r.1) hbase
    have h₂ : (helicoidTubeEquiv.symm (Y q)).2 = q.2 :=
      congrArg (fun r : ℝ × ℝ => r.2) hbase
    exact Prod.ext (Prod.ext rfl h₁) h₂
  have hright := helicoidTubeEquiv.right_inv hqY
  change helicoidTubeMap (helicoidTubeEquiv.symm (Y q)) = Y q at hright
  rw [hcoord] at hright
  exact hright.symm

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoid_surface_projection_local_diffeomorph
#print axioms TwoAxisHelicoid.helicoid_surface_local_normal_graph
