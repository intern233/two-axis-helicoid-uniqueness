import TwoAxisHelicoid.NormalGraphDerivativeConvergence

namespace TwoAxisHelicoid
open Set Filter
open scoped Topology ContDiff

/-- On a fixed core chart in a tube, the height and its first derivative
converge locally uniformly to zero if the actual parametrized surfaces
converge in the spatial C¹ topology. The tube coordinate is only required
to be smooth at the points used in the chart. -/
theorem spatial_C1_convergence_gives_tube_height_decay {U : Set ℂ} (hU : IsOpen U)
    (X : ℂ → EuclideanSpace ℝ (Fin 3)) (Z : ℕ → ℂ → EuclideanSpace ℝ (Fin 3))
    (signed : EuclideanSpace ℝ (Fin 3) → ℝ) (u : ℕ → ℂ → ℝ)
    (hX : ∀ z ∈ U, ContDiffAt ℝ 1 X z) (hZ : ∀ n z, z ∈ U → DifferentiableAt ℝ (Z n) z)
    (hδ : ∀ z ∈ U, ContDiffAt ℝ 1 signed (X z))
    (hδZ : ∀ n z, z ∈ U → DifferentiableAt ℝ signed (Z n z))
    (hzero : ∀ z ∈ U, signed (X z) = 0) (hu : ∀ n z, z ∈ U → u n z = signed (Z n z))
    (hv : TendstoLocallyUniformlyOn Z X atTop U)
    (hd : TendstoLocallyUniformlyOn (fun n => fderiv ℝ (Z n)) (fderiv ℝ X) atTop U) :
    (∀ n z, z ∈ U → DifferentiableAt ℝ (u n) z) ∧
    TendstoLocallyUniformlyOn u (fun _ => 0) atTop U ∧
    TendstoLocallyUniformlyOn (fun n => fderiv ℝ (u n)) (fun _ => 0) atTop U := by
  have Du (n : ℕ) (z : ℂ) (hz : z ∈ U) :
      HasFDerivAt (u n) ((fderiv ℝ signed (Z n z)).comp (fderiv ℝ (Z n) z)) z := by
    apply ((hδZ n z hz).hasFDerivAt.comp z (hZ n z hz).hasFDerivAt).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hu n w hw
  have Dz (z : ℂ) (hz : z ∈ U) : (fderiv ℝ signed (X z)).comp (fderiv ℝ X z) = 0 := by
    have e : signed ∘ X =ᶠ[𝓝 z] (fun _ => (0:ℝ)) := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact hzero w hw
    rw [← fderiv_comp z ((hδ z hz).differentiableAt one_ne_zero) ((hX z hz).differentiableAt one_ne_zero),e.fderiv_eq]
    simp
  have both (z : ℂ) (hz : z ∈ U) :
      let l := (atTop : Filter ℕ) ×ˢ 𝓝 z
      Tendsto (fun p : ℕ × ℂ => u p.1 p.2) l (𝓝 0) ∧
      Tendsto (fun p : ℕ × ℂ => fderiv ℝ (u p.1) p.2) l (𝓝 0) := by
    let l := (atTop : Filter ℕ) ×ˢ 𝓝 z
    have hs : Tendsto (fun p : ℕ × ℂ => Z p.1 p.2) l (𝓝 (X z)) :=
      ((hX z hz).continuousAt.tendsto.comp tendsto_snd).congr_uniformity
        ((hU.tendstoLocallyUniformlyOn_iff_forall_tendsto.mp hv) z hz)
    have hds : Tendsto (fun p : ℕ × ℂ => fderiv ℝ (Z p.1) p.2) l (𝓝 (fderiv ℝ X z)) :=
      (((hX z hz).continuousAt_fderiv one_ne_zero).tendsto.comp tendsto_snd).congr_uniformity
        ((hU.tendstoLocallyUniformlyOn_iff_forall_tendsto.mp hd) z hz)
    constructor
    · have h := (hδ z hz).continuousAt.tendsto.comp hs
      rw [hzero z hz] at h
      apply h.congr'
      filter_upwards [tendsto_snd (hU.mem_nhds hz)] with p hp
      exact (hu p.1 p.2 hp).symm
    · have hc : Continuous (fun p : (EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) × (ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3)) =>
          p.1.comp p.2) := continuous_fst.clm_comp continuous_snd
      have h := hc.continuousAt.tendsto.comp
        ((((hδ z hz).continuousAt_fderiv one_ne_zero).tendsto.comp hs).prodMk_nhds hds)
      change Tendsto _ _ (𝓝 ((fderiv ℝ signed (X z)).comp (fderiv ℝ X z))) at h
      rw [Dz z hz] at h
      apply h.congr'
      filter_upwards [tendsto_snd (hU.mem_nhds hz)] with p hp
      exact (Du p.1 p.2 hp).fderiv.symm
  refine ⟨fun n z hz => (Du n z hz).differentiableAt,?_,?_⟩
  · apply hU.tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr
    intro z hz
    exact (tendsto_const_nhds.prodMk_nhds (both z hz).1).mono_right (nhds_le_uniformity _)
  · apply hU.tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr
    intro z hz
    exact (tendsto_const_nhds.prodMk_nhds (both z hz).2).mono_right (nhds_le_uniformity _)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.spatial_C1_convergence_gives_tube_height_decay
