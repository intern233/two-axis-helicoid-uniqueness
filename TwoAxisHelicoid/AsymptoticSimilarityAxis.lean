import TwoAxisHelicoid.UniqueAsymptoticVerticalAxis
import TwoAxisHelicoid.SimilarityFlowMetric

namespace TwoAxisHelicoid
open Complex Matrix Set Filter Topology
open scoped Topology

/-- Every continuous affine similarity flow preserving a positionally
helicoidal set containing its vertical axis has vertical translation
and rotation velocities. This uses only the two positional straight
line rigidity lemmas. -/
theorem asymptotic_vertical_axis_similarity_velocities {S : Set (Fin 3 → ℝ)} {α : ℝ}
    (hα : α ≠ 0) (hend : ApproachesSetAtInfinity S (range (axisRuledHelicoid I α 0)))
    (axis : ∀ h : ℝ, (![0,0,h] : Fin 3 → ℝ) ∈ S)
    (a b : Fin 3 → ℝ) (d : ℝ)
    (pres : ∀ t : ℝ, MapsTo (affineAmbientFlow (similarityLinear b d) a t) S S) :
    a 0=0 ∧ a 1=0 ∧ b 0=0 ∧ b 1=0 := by
  let ez : Fin 3 → ℝ := ![0,0,1]
  let L := similarityLinear b d
  let O := fun t : ℝ => affineAmbientFlow L a t 0
  let W := fun t : ℝ => affineAmbientLinearPart L a t ez
  have O0 : O 0=0 := affineAmbientFlow_zero _ _ _
  have W0 : W 0=ez := by
    have e := affineAmbientFlow_linear_part L a ez 0
    simpa only [affineAmbientFlow_zero,add_zero] using e.symm
  have dO : HasDerivAt O a 0 := by simpa only [O,affineAmbientFlow_zero,map_zero,add_zero] using affineAmbientFlow_deriv L a (0:Fin 3 → ℝ) 0
  have dW : HasDerivAt W (L ez) 0 := by
    change HasDerivAt (fun t => affineAmbientLinearPart L a t ez) (L ez) 0
    simpa only [show affineAmbientLinearPart L a 0 ez=ez from W0] using affineAmbientLinearPart_deriv L a ez 0
  have step : ∀ᶠ t in 𝓝 (0:ℝ), W t 2 ≠ 0 :=
    ((continuous_apply 2).continuousAt.comp dW.continuousAt).eventually_ne (by change W 0 2 ≠ 0; rw [W0]; norm_num [ez])
  have vanish : ∀ᶠ t in 𝓝 (0:ℝ), O t 0=0 ∧ O t 1=0 ∧ W t 0=0 ∧ W t 1=0 := by
    filter_upwards [step] with t hn
    have line (u : ℝ) : O t+u • W t ∈ S := by
      have pos := pres t (axis u)
      have e : (![0,0,u] : Fin 3 → ℝ)=u • ez := by ext j; fin_cases j <;> simp [ez]
      rwa [e,affineAmbientFlow_linear_part,map_smul,add_comm] at pos
    obtain ⟨w0,w1⟩ := (line_approaching_helicoid_horizontal_or_vertical hα hend (O t) (W t) line).resolve_left hn
    have cent := vertical_line_in_helicoid_end_is_central hα hend (O t 0) (O t 1) (by
      intro h
      let u := (h-O t 2)/W t 2
      have eq : O t+u • W t = ![O t 0,O t 1,h] := by
        ext j
        fin_cases j
        · simp [w0]
        · simp [w1]
        · change O t 2+u*W t 2=h
          dsimp [u]
          field_simp
          ring
      exact eq ▸ line u)
    exact ⟨cent.1,cent.2,w0,w1⟩
  have derivative_zero {f : ℝ → Fin 3 → ℝ} {v : Fin 3 → ℝ} (hd : HasDerivAt f v 0) (j : Fin 3)
      (h : ∀ᶠ t in 𝓝 (0:ℝ), f t j=0) : v j=0 := by
    let pr := (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ)
    have eq := (pr.hasFDerivAt.comp_hasDerivAt 0 hd).deriv
    have germ : (fun t => f t j) =ᶠ[𝓝 (0:ℝ)] fun _ => (0:ℝ) := h
    exact eq.symm.trans (germ.deriv_eq.trans (deriv_const _ _))
  have ew0 := derivative_zero dW 0 (vanish.mono fun _ h => h.2.2.1)
  have ew1 := derivative_zero dW 1 (vanish.mono fun _ h => h.2.2.2)
  refine ⟨derivative_zero dO 0 (vanish.mono fun _ h => h.1),derivative_zero dO 1 (vanish.mono fun _ h => h.2.1),?_,?_⟩
  · simpa [L,ez,similarityLinear_apply,cross_apply] using ew1
  · simpa [L,ez,similarityLinear_apply,cross_apply] using ew0

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.asymptotic_vertical_axis_similarity_velocities
