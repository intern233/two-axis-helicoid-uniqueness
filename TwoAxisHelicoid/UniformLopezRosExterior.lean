import TwoAxisHelicoid.UniformExteriorDoublePoints
import TwoAxisHelicoid.MarkedExteriorDeformedDerivative
import TwoAxisHelicoid.WeierstrassSimilarity

namespace TwoAxisHelicoid
open Complex Set Filter Topology Bornology
open scoped Topology

/-- On each compact logarithmic multiplier interval every double point
is confined to a single compact set of parameter pairs. A constant phase
of the exterior Weierstrass coordinate is removed by a fixed spatial
rotation, including when the logarithmic correction is nonzero at infinity. -/
theorem compact_double_points_of_exponential_end_family {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M ℂ) {r₀ r : ℝ} (ht : e.target = {z : ℂ | r₀ < ‖z‖})
    (core : IsCompact e.sourceᶜ) (esc : Tendsto (fun p => ‖e p‖) (cocompact M) atTop) (hr : r₀<r)
    (W : ℝ → M → Fin 3 → ℝ) (cont : Continuous (fun p : ℝ × M => W p.1 p.2))
    (α b : ℝ) (F : ℂ → ℂ) (hF : AnalyticAt ℂ F 0)
    (der : ∀ z : ℂ, r < ‖z‖ → ∀ s : ℝ, HasFDerivAt (W s ∘ e.symm)
      (nullRealDerivative (weierstrassTriple ((Real.exp s:ℂ)*exp (I*α*z+F z⁻¹)) 1)) z)
    (height : ∀ s (z : ℂ), r<‖z‖ → W s (e.symm z) 2=z.re+b) {K : Set ℝ} (hK : IsCompact K) :
    ∃ C : Set M, IsCompact C ∧ ∀ s ∈ K, immersionDoublePoints (W s) ⊆ C ×ˢ C := by
  let c := Complex.exp ((-(F 0).im:ℝ)*I)
  have hc : ‖c‖=1 := Complex.norm_exp_ofReal_mul_I _
  let U := fun s : ℝ => verticalRotation c ∘ W s
  let X := fun s : ℝ => U s ∘ e.symm
  let G := fun z : ℂ => F z⁻¹-F 0
  let f := fun (s : ℝ) (z : ℂ) => G z+((F 0).re:ℂ)+(s:ℂ)
  have cu : Continuous (fun p : ℝ × M => U p.1 p.2) := (verticalRotation c).continuous.comp cont
  have decay : Tendsto G (cobounded ℂ) (𝓝 0) := by
    simpa only [G,Function.comp_apply,sub_self] using (hF.continuousAt.tendsto.comp tendsto_inv₀_cobounded).sub_const (F 0)
  obtain ⟨Y,hY,hy,small⟩ := helicoidal_correction_small_phase decay r
  have cx (s : ℝ) (z : ℂ) (hz : r<‖z‖) : ContinuousAt (fun p : ℝ × ℂ => X p.1 p.2) (s,z) := by
    have ce := e.symm.continuousAt (show z ∈ e.target from ht ▸ hr.trans hz)
    apply cu.continuousAt.comp (x := (s,z)) (f := fun p : ℝ × ℂ => (p.1,e.symm p.2))
    exact continuous_fst.continuousAt.prodMk (ce.comp continuous_snd.continuousAt)
  have dx (s : ℝ) (z : ℂ) (hz : r<‖z‖) : HasFDerivAt (X s)
      (nullRealDerivative (weierstrassTriple (exp (I*α*z+f s z)) 1)) z := by
    have factors : exp (I*α*z+f s z)=c*((Real.exp s:ℂ)*exp (I*α*z+F z⁻¹)) := by
      dsimp only [c]
      rw [Complex.ofReal_exp,← Complex.exp_add,← Complex.exp_add]
      apply congrArg Complex.exp
      have repr := Complex.re_add_im (F 0)
      dsimp only [f,G]
      push_cast
      linear_combination repr
    rw [factors,nullRealDerivative_unit_multiplier hc]
    exact (verticalRotation c).hasFDerivAt.comp z (der z hz s)
  have hh (s : ℝ) (z : ℂ) (hz : r<‖z‖) : X s z 2=z.re+b := height s z hz
  have phase (s : ℝ) (z : ℂ) (hz : Y ≤ ‖z‖) : |(f s z).im| ≤ 1 := by
    simpa only [f,Complex.add_im,Complex.ofReal_im,add_zero] using small z hz
  obtain ⟨⟨R,hR,inj⟩,bounded⟩ := compact_family_helicoidal_end_control hK X f α b r Y hY.le hy
    (fun s _ => cx s) (fun s _ => dx s) (fun s _ => hh s) (fun s _ => phase s)
  obtain ⟨C,hC,hbound⟩ := compact_family_exterior_double_points hK e core esc U
    (fun _ _ _ => cu.continuousAt) hR inj bounded
  refine ⟨C,hC,?_⟩
  intro s hs pair hp
  exact hbound s hs ⟨congrArg (verticalRotation c) hp.1,hp.2⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_double_points_of_exponential_end_family
