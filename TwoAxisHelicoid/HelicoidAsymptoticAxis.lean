import TwoAxisHelicoid.HelicoidAsymptoticLines

namespace TwoAxisHelicoid
open Complex Matrix Set
open scoped Topology
set_option maxHeartbeats 1600000

/-- Two nonzero orthogonal vectors which are each horizontal or
vertical and whose sum has the same dichotomy must both be horizontal. -/
theorem helicoid_ruling_plane_horizontal (U V : Fin 3 → ℝ)
    (hU : U ≠ 0) (hV : V ≠ 0) (huv : U ⬝ᵥ V = 0)
    (hu : U 2 = 0 ∨ U 0 = 0 ∧ U 1 = 0)
    (hv : V 2 = 0 ∨ V 0 = 0 ∧ V 1 = 0)
    (hs : (U+V) 2 = 0 ∨ (U+V) 0 = 0 ∧ (U+V) 1 = 0) : U 2 = 0 ∧ V 2 = 0 := by
  have hn (A : Fin 3 → ℝ) (hA : A ≠ 0) (h₀ : A 0 = 0) (h₁ : A 1 = 0) : A 2 ≠ 0 := by
    intro h₂
    apply hA
    ext j
    fin_cases j <;> assumption
  simp only [Pi.add_apply] at hs
  rcases hu with hu | ⟨hu₀,hu₁⟩ <;> rcases hv with hv | ⟨hv₀,hv₁⟩
  · exact ⟨hu,hv⟩
  · rcases hs with hs | ⟨hs₀,hs₁⟩
    · exact ⟨hu,by linarith⟩
    · exact False.elim ((hn U hU (by linarith) (by linarith)) hu)
  · rcases hs with hs | ⟨hs₀,hs₁⟩
    · exact ⟨by linarith,hv⟩
    · exact False.elim ((hn V hV (by linarith) (by linarith)) hv)
  · have h₁ := hn U hU hu₀ hu₁
    have h₂ := hn V hV hv₀ hv₁
    simp [dotProduct,Fin.sum_univ_succ,hu₀,hu₁,hv₀,hv₁,h₁,h₂] at huv

theorem vertical_of_perpendicular_to_horizontal_basis (U V W : Fin 3 → ℝ)
    (hu : U 2 = 0) (hv : V 2 = 0) (huu : U ⬝ᵥ U = 1) (hvv : V ⬝ᵥ V = 1)
    (huv : U ⬝ᵥ V = 0) (huw : U ⬝ᵥ W = 0) (hvw : V ⬝ᵥ W = 0) : W 0 = 0 ∧ W 1 = 0 := by
  simp [dotProduct,Fin.sum_univ_succ,hu,hv] at huu hvv huv huw hvw
  have hd : U 0*V 1-U 1*V 0 ≠ 0 := by
    intro he
    have hh : (U 0*V 1-U 1*V 0)^2 =
        (U 0*U 0+U 1*U 1)*(V 0*V 0+V 1*V 1)-(U 0*V 0+U 1*V 1)^2 := by ring
    rw [he,huu,hvv,huv] at hh
    norm_num at hh
  constructor
  · have hz : (U 0*V 1-U 1*V 0)*W 0 = 0 := by linear_combination V 1*huw-U 1*hvw
    exact (mul_eq_zero.mp hz).resolve_left hd
  · have hz : (U 0*V 1-U 1*V 0)*W 1 = 0 := by linear_combination U 0*hvw-V 0*huw
    exact (mul_eq_zero.mp hz).resolve_left hd

/-- In reference coordinates in which the second helicoid is vertical,
a placed first helicoid that approaches it in positional distance has
parallel axis. The placement may translate or apply any orthogonal
linear map and either pitch may have either sign. -/
theorem asymptotic_helicoids_axes_parallel (L : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))
    (hL : ∀ u v : Fin 3 → ℝ, L u ⬝ᵥ L v = u ⬝ᵥ v) (P : Fin 3 → ℝ) (α β : ℝ)
    (hα : α ≠ 0) (hβ : β ≠ 0)
    (h : ApproachesSetAtInfinity ((fun y => P+L y) '' range (axisRuledHelicoid I β 0))
      (range (axisRuledHelicoid I α 0))) :
    L ![0,0,1] 0 = 0 ∧ L ![0,0,1] 1 = 0 := by
  let e₁ : Fin 3 → ℝ := ![1,0,0]
  let e₂ : Fin 3 → ℝ := ![0,1,0]
  let e₃ : Fin 3 → ℝ := ![0,0,1]
  have hline (θ r : ℝ) :
      P+(θ/β) • L e₃ + r • L ((Real.cos θ) • e₁ + (Real.sin θ) • e₂) ∈
        (fun y => P+L y) '' range (axisRuledHelicoid I β 0) := by
    refine ⟨axisRuledHelicoid I β 0 ⟨r,θ/β⟩,⟨_,rfl⟩,?_⟩
    rw [axisRuledHelicoid_standard_ruling]
    change P+L ![r*Real.cos (β*(θ/β)),r*Real.sin (β*(θ/β)),θ/β] = _
    rw [show β*(θ/β)=θ by field_simp]
    have he : (![r*Real.cos θ,r*Real.sin θ,θ/β] : Fin 3 → ℝ) =
        (θ/β) • e₃+r • (Real.cos θ • e₁+Real.sin θ • e₂) := by
      ext i
      fin_cases i <;> simp [e₁,e₂,e₃]
    rw [he,map_add,map_smul,map_smul,add_assoc]
  have hh (θ : ℝ) := line_approaching_helicoid_horizontal_or_vertical hα h _ _ (hline θ)
  have hx := hh 0
  have hy := hh (Real.pi/2)
  have hdiag := hh (Real.pi/4)
  simp only [Real.cos_zero,Real.sin_zero,one_smul,zero_smul,add_zero] at hx
  simp only [Real.cos_pi_div_two,Real.sin_pi_div_two,zero_smul,one_smul,zero_add] at hy
  have hs : Real.sin (Real.pi/4) = Real.cos (Real.pi/4) := by rw [Real.sin_pi_div_four,Real.cos_pi_div_four]
  have hc : Real.cos (Real.pi/4) ≠ 0 := (Real.cos_pos_of_mem_Ioo (by constructor <;> linarith [Real.pi_pos])).ne'
  rw [hs,← smul_add,map_smul,map_add] at hdiag
  simp only [Pi.smul_apply,smul_eq_mul,mul_eq_zero,or_iff_right hc] at hdiag
  have u := hL e₁ e₁
  have v := hL e₂ e₂
  have uv := hL e₁ e₂
  have uw := hL e₁ e₃
  have vw := hL e₂ e₃
  have huu : L e₁ ⬝ᵥ L e₁ = 1 := u.trans (by norm_num [e₁,dotProduct,Fin.sum_univ_succ])
  have hvv : L e₂ ⬝ᵥ L e₂ = 1 := v.trans (by norm_num [e₂,dotProduct,Fin.sum_univ_succ])
  have huv : L e₁ ⬝ᵥ L e₂ = 0 := uv.trans (by norm_num [e₁,e₂,dotProduct,Fin.sum_univ_succ])
  have huw : L e₁ ⬝ᵥ L e₃ = 0 := uw.trans (by norm_num [e₁,e₃,dotProduct,Fin.sum_univ_succ])
  have hvw : L e₂ ⬝ᵥ L e₃ = 0 := vw.trans (by norm_num [e₂,e₃,dotProduct,Fin.sum_univ_succ])
  have hU : L e₁ ≠ 0 := by intro hh'; simp [hh'] at huu
  have hV : L e₂ ≠ 0 := by intro hh'; simp [hh'] at hvv
  obtain ⟨hu,hv⟩ := helicoid_ruling_plane_horizontal _ _ hU hV huv hx hy hdiag
  exact vertical_of_perpendicular_to_horizontal_basis _ _ _ hu hv huu hvv huv huw hvw

/-- On the same surface end, inclusion at arbitrarily small distances
from the first helicoid to the end and from the end to the second
helicoid already identifies their axis direction. -/
theorem helicoid_axis_alignment_through_surface {S : Set (Fin 3 → ℝ)}
    (L : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) (hL : ∀ u v, L u ⬝ᵥ L v = u ⬝ᵥ v)
    (P : Fin 3 → ℝ) (α β : ℝ) (hα : α ≠ 0) (hβ : β ≠ 0)
    (h₁ : ApproachesSetAtInfinity ((fun y => P+L y) '' range (axisRuledHelicoid I β 0)) S)
    (h₂ : ApproachesSetAtInfinity S (range (axisRuledHelicoid I α 0))) :
    L ![0,0,1] 0 = 0 ∧ L ![0,0,1] 1 = 0 :=
  asymptotic_helicoids_axes_parallel L hL P α β hα hβ (h₁.trans h₂)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.helicoid_axis_alignment_through_surface
