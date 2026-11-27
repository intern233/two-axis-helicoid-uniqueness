import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

namespace TwoAxisHelicoid
open Set Filter
open scoped Topology ContDiff

/-- In a fixed chart of a limit surface, local C¹ decay of normal
graph heights implies local uniform convergence of the spatial
derivatives. The graph formula need hold only on the chart domain. -/
theorem normal_graph_spatial_derivative_convergence {U : Set ℂ} (hU : IsOpen U)
    (X N : ℂ → EuclideanSpace ℝ (Fin 3)) (Z : ℕ → ℂ → EuclideanSpace ℝ (Fin 3)) (u : ℕ → ℂ → ℝ)
    (hX : ∀ z ∈ U, ContDiffAt ℝ 1 X z) (hN : ∀ z ∈ U, ContDiffAt ℝ 1 N z)
    (hu : ∀ n z, z ∈ U → DifferentiableAt ℝ (u n) z) (he : ∀ n z, z ∈ U → Z n z = X z+u n z • N z)
    (h₀ : TendstoLocallyUniformlyOn u (fun _ => 0) atTop U)
    (h₁ : TendstoLocallyUniformlyOn (fun n => fderiv ℝ (u n)) (fun _ => 0) atTop U) :
    (∀ n z, z ∈ U → DifferentiableAt ℝ (Z n) z) ∧
    TendstoLocallyUniformlyOn (fun n => fderiv ℝ (Z n)) (fderiv ℝ X) atTop U := by
  have D (n : ℕ) (z : ℂ) (hz : z ∈ U) :
      HasFDerivAt (Z n) (fderiv ℝ X z+(u n z • fderiv ℝ N z+(fderiv ℝ (u n) z).smulRight (N z))) z := by
    have e : Z n =ᶠ[𝓝 z] (fun w => X w+u n w • N w) := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact he n w hw
    exact (((hX z hz).differentiableAt one_ne_zero).hasFDerivAt.add
      ((hu n z hz).hasFDerivAt.smul ((hN z hz).differentiableAt one_ne_zero).hasFDerivAt)).congr_of_eventuallyEq e
  refine ⟨fun n z hz => (D n z hz).differentiableAt,?_⟩
  apply hU.tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr
  intro z hz
  let l := (atTop : Filter ℕ) ×ˢ 𝓝 z
  have hval : Tendsto (fun p : ℕ × ℂ => u p.1 p.2) l (𝓝 0) :=
    tendsto_const_nhds.congr_uniformity ((hU.tendstoLocallyUniformlyOn_iff_forall_tendsto.mp h₀) z hz)
  have hder : Tendsto (fun p : ℕ × ℂ => fderiv ℝ (u p.1) p.2) l (𝓝 0) :=
    tendsto_const_nhds.congr_uniformity ((hU.tendstoLocallyUniformlyOn_iff_forall_tendsto.mp h₁) z hz)
  have nv : Tendsto (fun p : ℕ × ℂ => N p.2) l (𝓝 (N z)) := (hN z hz).continuousAt.tendsto.comp tendsto_snd
  have nd : Tendsto (fun p : ℕ × ℂ => fderiv ℝ N p.2) l (𝓝 (fderiv ℝ N z)) :=
    ((hN z hz).continuousAt_fderiv one_ne_zero).tendsto.comp tendsto_snd
  have xd : Tendsto (fun p : ℕ × ℂ => fderiv ℝ X p.2) l (𝓝 (fderiv ℝ X z)) :=
    ((hX z hz).continuousAt_fderiv one_ne_zero).tendsto.comp tendsto_snd
  have ht : Tendsto (fun p : ℕ × ℂ => (fderiv ℝ (u p.1) p.2).smulRight (N p.2)) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [ContinuousLinearMap.norm_smulRight_apply,norm_zero,zero_mul] using hder.norm.mul nv.norm
  have hzD : Tendsto (fun p : ℕ × ℂ => fderiv ℝ (Z p.1) p.2) l (𝓝 (fderiv ℝ X z)) := by
    have h := xd.add ((hval.smul nd).add ht)
    have hzero : (0:ℝ) • fderiv ℝ N z = 0 := by ext v; simp
    rw [hzero,add_zero,add_zero] at h
    apply h.congr'
    filter_upwards [tendsto_snd (hU.mem_nhds hz)] with p hp
    exact (D p.1 p.2 hp).fderiv.symm
  exact (xd.prodMk_nhds hzD).mono_right (nhds_le_uniformity _)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.normal_graph_spatial_derivative_convergence
