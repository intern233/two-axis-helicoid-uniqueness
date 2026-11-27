import TwoAxisHelicoid.HelicoidAsymptoticLines

namespace TwoAxisHelicoid
open Complex Matrix Set Filter Topology
open scoped Topology

/-- If a surface asymptotically contains an escaping affine ray and lies
in a fixed plane, the plane normal is orthogonal to that ray. -/
theorem plane_normal_orthogonal_to_asymptotic_ray {S T : Set (Fin 3 → ℝ)}
    (h : ApproachesSetAtInfinity T S) (hS : S.Nonempty) (A W n : Fin 3 → ℝ) (b : ℝ)
    (hn : ∀ p ∈ S, n ⬝ᵥ p = b) (hW : W ≠ 0) (hr : ∀ r : ℝ, A+r • W ∈ T) : n ⬝ᵥ W = 0 := by
  obtain ⟨q,hq,hlim⟩ := h.exists_sequence hS (fun k : ℕ => hr ((k:ℝ)+1)) (affine_ray_norm_tendsto_atTop A W hW)
  have hnlim : Tendsto (fun k : ℕ => fun j => q k j/((k:ℝ)+1)) atTop (𝓝 W) :=
    tendsto_pi_nhds.mpr (fun j => affine_ray_normalized_coordinate_limit A W hlim j)
  have hf : Continuous (fun v : Fin 3 → ℝ => n ⬝ᵥ v) := by unfold dotProduct; fun_prop
  have hz := (tendsto_const_nhds (x := b)).mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have he (k : ℕ) : n ⬝ᵥ (fun j => q k j/((k:ℝ)+1)) = b*(1/((k:ℝ)+1)) := by
    rw [← hn _ (hq k)]
    simp only [dotProduct,Finset.sum_mul,div_eq_mul_inv,mul_assoc,one_mul]
  apply tendsto_nhds_unique (hf.continuousAt.tendsto.comp hnlim)
  simp only [Function.comp_def]
  simpa only [mul_zero] using (show Tendsto (fun k : ℕ => b*(1/((k:ℝ)+1))) atTop (𝓝 (b*0)) from hz).congr
    (fun k => (he k).symm)

/-- A positional asymptote to a nonzero-pitch helicoid is nonplanar.
The three independent ray directions suffice, including two horizontal
rulings at different heights. -/
theorem helicoid_asymptotic_surface_nonplanar {S : Set (Fin 3 → ℝ)} {α : ℝ} (hα : α ≠ 0)
    (h : ApproachesSetAtInfinity (range (axisRuledHelicoid I α 0)) S) (hs : S.Nonempty) :
    ¬ ∃ (n : Fin 3 → ℝ) (b : ℝ), n ≠ 0 ∧ ∀ p ∈ S, n ⬝ᵥ p = b := by
  rintro ⟨n,b,hn,hp⟩
  have hdir (θ : ℝ) : n ⬝ᵥ ![Real.cos θ,Real.sin θ,0] = 0 := by
    let W : Fin 3 → ℝ := ![Real.cos θ,Real.sin θ,0]
    have hW : W ≠ 0 := by
      intro hw
      have h₁ : Real.cos θ = 0 := congrFun hw 0
      have h₂ : Real.sin θ = 0 := congrFun hw 1
      have h := Real.sin_sq_add_cos_sq θ
      rw [h₁,h₂] at h
      norm_num at h
    apply plane_normal_orthogonal_to_asymptotic_ray h hs ![0,0,θ/α] W n b hp hW
    intro r
    refine ⟨⟨r,θ/α⟩,?_⟩
    rw [axisRuledHelicoid_standard_ruling]
    ext j
    fin_cases j <;> simp [W,mul_div_cancel₀ θ hα]
  have h₃ : n ⬝ᵥ ![0,0,1] = 0 := by
    apply plane_normal_orthogonal_to_asymptotic_ray h hs 0 ![0,0,1] n b hp (by
      intro hh; exact one_ne_zero (congrFun hh 2))
    intro r
    refine ⟨⟨0,r⟩,?_⟩
    rw [axisRuledHelicoid_standard_ruling]
    ext j
    fin_cases j <;> simp
  apply hn
  have hx : n 0 = 0 := by simpa [dotProduct,Fin.sum_univ_succ] using hdir 0
  have hy : n 1 = 0 := by simpa [dotProduct,Fin.sum_univ_succ] using hdir (Real.pi/2)
  have hz : n 2 = 0 := by simpa [dotProduct,Fin.sum_univ_succ] using h₃
  ext j
  fin_cases j <;> assumption

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.helicoid_asymptotic_surface_nonplanar
