import TwoAxisHelicoid.CoordinateAreaHessian
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
namespace TwoAxisHelicoid
open Set Filter MeasureTheory
open scoped Topology

theorem hasDerivAt_compact_plane_integral
    {F F' : ℝ → ℝ × ℝ → ℝ} {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    {l u x : ℝ} (hx : x ∈ Ioo l u)
    (hc : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => F p.1 p.2) (Icc l u ×ˢ K))
    (hc' : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => F' p.1 p.2) (Icc l u ×ˢ K))
    (hd : ∀ s ∈ Ioo l u, ∀ p ∈ K, HasDerivAt (fun r => F r p) (F' s p) s) :
    HasDerivAt (fun r => ∫ p in K, F r p) (∫ p in K, F' x p) x := by
  have hsection (s : ℝ) (hs : s ∈ Icc l u) : ContinuousOn (F s) K :=
    hc.comp (f := fun p : ℝ × ℝ => (s,p)) (by fun_prop) (fun _ hp => ⟨hs,hp⟩)
  have hsection' (s : ℝ) (hs : s ∈ Icc l u) : ContinuousOn (F' s) K :=
    hc'.comp (f := fun p : ℝ × ℝ => (s,p)) (by fun_prop) (fun _ hp => ⟨hs,hp⟩)
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hc'
  have hx' : x ∈ Icc l u := ⟨hx.1.le,hx.2.le⟩
  let μ : Measure (ℝ × ℝ) := volume.restrict K
  have hmeas : ∀ᶠ s in 𝓝 x, AEStronglyMeasurable (F s) μ := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with s hs
    exact (hsection s ⟨hs.1.le,hs.2.le⟩).aestronglyMeasurable hK.measurableSet
  have hint : Integrable (F x) μ := (hsection x hx').integrableOn_compact hK
  have hmeas' : AEStronglyMeasurable (F' x) μ :=
    (hsection' x hx').aestronglyMeasurable hK.measurableSet
  have hbound : ∀ᵐ p ∂μ, ∀ s ∈ Ioo l u, ‖F' s p‖ ≤ M := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
    intro s hs
    exact hM (s,p) ⟨⟨hs.1.le,hs.2.le⟩,hp⟩
  have hdiff : ∀ᵐ p ∂μ, ∀ s ∈ Ioo l u, HasDerivAt (fun r => F r p) (F' s p) s := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
    exact fun s hs => hd s hs p hp
  have hmInt : Integrable (fun _ : ℝ × ℝ => M) μ := by
    change IntegrableOn (fun _ : ℝ × ℝ => M) K volume
    exact integrableOn_const (ne_of_lt hK.measure_lt_top)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun _ => M) (μ := μ)
    (isOpen_Ioo.mem_nhds hx) hmeas hint hmeas' hbound hmInt hdiff).2

theorem second_derivative_compact_plane_integral
    {F F' F'' : ℝ → ℝ × ℝ → ℝ} {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    {l u x : ℝ} (hx : x ∈ Ioo l u)
    (hc : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => F p.1 p.2) (Icc l u ×ˢ K))
    (hc' : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => F' p.1 p.2) (Icc l u ×ˢ K))
    (hc'' : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => F'' p.1 p.2) (Icc l u ×ˢ K))
    (hd : ∀ s ∈ Ioo l u, ∀ p ∈ K, HasDerivAt (fun r => F r p) (F' s p) s)
    (hd' : ∀ s ∈ Ioo l u, ∀ p ∈ K, HasDerivAt (fun r => F' r p) (F'' s p) s) :
    HasDerivAt (deriv (fun r => ∫ p in K, F r p)) (∫ p in K, F'' x p) x := by
  have he : deriv (fun r => ∫ p in K, F r p) =ᶠ[𝓝 x] (fun r => ∫ p in K, F' r p) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with s hs
    exact (hasDerivAt_compact_plane_integral hK hs hc hc' hd).deriv
  exact (hasDerivAt_compact_plane_integral hK hx hc' hc'' hd').congr_of_eventuallyEq he

noncomputable def coordinateVariationDensity
    (X : ℂ → Fin 3 → ℝ) (W : ℂ → ℂ) (v : ℝ × ℝ → ℝ) (s : ℝ) (p : ℝ × ℝ) : ℝ :=
  coordinateAreaDensity (weierstrassNormalVariation X W (scalarComplexLift v) s) (planeComplex p)

/-- Second derivative of an actual finite-patch area integral. Joint
continuity of the first two parameter derivatives supplies uniform
domination, and pointwise C2 regularity is stated explicitly. Establishing
these hypotheses for every candidate surface remains a separate task. -/
theorem compact_actual_area_second_variation
    {X : ℂ → Fin 3 → ℝ} {W : ℂ → ℂ} {v : ℝ × ℝ → ℝ}
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hsupport : tsupport v ⊆ K)
    {l u : ℝ} (h0 : (0 : ℝ) ∈ Ioo l u)
    (hc : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => coordinateVariationDensity X W v q.1 q.2)
      (Icc l u ×ˢ K))
    (hc' : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      deriv (fun s => coordinateVariationDensity X W v s q.2) q.1) (Icc l u ×ˢ K))
    (hc'' : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      deriv (deriv (fun s => coordinateVariationDensity X W v s q.2)) q.1) (Icc l u ×ˢ K))
    (hreg : ∀ s ∈ Ioo l u, ∀ p ∈ K,
      ContDiffAt ℝ 2 (fun r => coordinateVariationDensity X W v r p) s)
    (hv : Differentiable ℝ v)
    (hX : ∀ p ∈ tsupport v, HasFDerivAt X
      (nullRealDerivative (weierstrassTriple (Complex.exp (W (planeComplex p))) 1)) (planeComplex p))
    (hW : ∀ p ∈ tsupport v, DifferentiableAt ℂ W (planeComplex p)) :
    HasDerivAt (deriv (fun s => ∫ p in K, coordinateVariationDensity X W v s p))
      (planarQuadraticEnergy (gaussNormalDirichletDensity W) v) 0 := by
  have hd (s : ℝ) (hs : s ∈ Ioo l u) (p : ℝ × ℝ) (hp : p ∈ K) :=
    ((hreg s hs p hp).differentiableAt (by norm_num)).hasDerivAt
  have hd' (s : ℝ) (hs : s ∈ Ioo l u) (p : ℝ × ℝ) (hp : p ∈ K) :
      HasDerivAt (deriv (fun r => coordinateVariationDensity X W v r p))
        (deriv (deriv (fun r => coordinateVariationDensity X W v r p)) s) s := by
    have h : ContDiffAt ℝ 1 (deriv (fun r => coordinateVariationDensity X W v r p)) s := by
      exact (hreg s hs p hp).derivWithin (m := 1) (by norm_num)
    exact (h.differentiableAt (by norm_num)).hasDerivAt
  have h := second_derivative_compact_plane_integral hK h0 hc hc' hc'' hd hd'
  have hi : (∫ p in K, coordinateNormalAreaHessian X W v p) =
      integratedCoordinateAreaHessian X W v := by
    rw [← integral_indicator hK.measurableSet]
    unfold integratedCoordinateAreaHessian
    congr 1
    funext p
    by_cases hp : p ∈ K
    · exact indicator_of_mem hp _
    · rw [indicator_of_notMem hp]
      exact (coordinateNormalAreaHessian_zero_off_support X W
        (fun hmem => hp (hsupport hmem))).symm
  change HasDerivAt _ (∫ p in K, coordinateNormalAreaHessian X W v p) 0 at h
  rw [hi,integratedCoordinateAreaHessian_eq_planar hv hX hW] at h
  exact h

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.compact_actual_area_second_variation
