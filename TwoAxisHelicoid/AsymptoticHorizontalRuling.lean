import TwoAxisHelicoid.HelicoidAsymptoticLines
import TwoAxisHelicoid.ReferenceHelicoidEnd
import TwoAxisHelicoid.HorizontalLineCoordinates

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology ComplexConjugate

theorem standard_graph_approaches_ruled {M : Type*} [TopologicalSpace M] {Y : M → Fin 3 → ℝ}
    (cont : Continuous Y) (graph : HasHelicoidC1End (coordinateToTube ∘ Y)) :
    ApproachesSetAtInfinity (range Y) (range (axisRuledHelicoid I 1 0)) := by
  have h := (graph.positional_asymptote (coordinateToTube.continuous.comp cont)).1
  have surf : tubeCartesian ∘ (coordinateToTube ∘ Y)=Y := funext fun x => tubeCartesian_coordinateToTube _
  have hel : range (fun p : ℝ × ℝ => standardHelicoid p.1 p.2)=range (axisRuledHelicoid I 1 0) := by
    ext v
    constructor
    · rintro ⟨⟨r,θ⟩,rfl⟩
      exact ⟨⟨r,θ⟩,by rw [axisRuledHelicoid_standard_ruling]; simp [standardHelicoid]⟩
    · rintro ⟨z,rfl⟩
      exact ⟨(z.re,z.im),by rw [axisRuledHelicoid_standard_ruling]; simp [standardHelicoid]⟩
  change ApproachesSetAtInfinity (range (tubeCartesian ∘ (coordinateToTube ∘ Y))) _ at h
  rwa [surf,hel] at h

/-- A complete horizontal line on a positionally asymptotic surface
has the ruling direction at the actual height of that line. -/
theorem horizontal_line_tangent_to_ruling {S : Set (Fin 3 → ℝ)} {α : ℝ}
    (h : ApproachesSetAtInfinity S (range (axisRuledHelicoid I α 0))) (B : Fin 3 → ℝ)
    (v : ℂ) (unit : ‖v‖=1) (line : ∀ r : ℝ, B+r • ![v.re,v.im,0]∈S) :
    v.re*Real.sin (α*B 2)=v.im*Real.cos (α*B 2) := by
  let W : Fin 3 → ℝ := ![v.re,v.im,0]
  let p := fun n : ℕ => B+((n:ℝ)+1) • W
  have non : W≠0 := by
    intro zero
    have x := congrFun zero 0
    have y := congrFun zero 1
    have vz : v=0 := Complex.ext (show v.re=0 from x) (show v.im=0 from y)
    simp [vz] at unit
  obtain ⟨q,hq,hnear⟩ := h.exists_sequence (range_nonempty _) (fun n : ℕ => line ((n:ℝ)+1)) (affine_ray_norm_tendsto_atTop B W non)
  have hh : Tendsto (fun n : ℕ => q n 2-p n 2) atTop (𝓝 0) := (continuous_apply (2:Fin 3)).continuousAt.tendsto.comp hnear
  have z2 (n : ℕ) : p n 2=B 2 := by change B 2+((n:ℝ)+1)*0=B 2; ring
  have height : Tendsto (fun n : ℕ => q n 2) atTop (𝓝 (B 2)) := by
    have k := hh.add (tendsto_const_nhds (x := B 2))
    simpa only [z2,sub_add_cancel,zero_add] using k
  have phase := (tendsto_const_nhds (x := α)).mul height
  have hx := (affine_ray_normalized_coordinate_limit B W hnear 0).mul (Real.continuous_sin.continuousAt.tendsto.comp phase)
  have hy := (affine_ray_normalized_coordinate_limit B W hnear 1).mul (Real.continuous_cos.continuousAt.tendsto.comp phase)
  apply tendsto_nhds_unique hx (hy.congr fun n => ?_)
  change q n 1/((n:ℝ)+1)*Real.cos (α*q n 2)=q n 0/((n:ℝ)+1)*Real.sin (α*q n 2)
  linear_combination -(normalized_helicoid_side_identity (hq n))/((n:ℝ)+1)

theorem same_span_ruling_vector {v : ℂ} (unit : ‖v‖=1) (h : ℝ)
    (parallel : v.re*Real.sin h=v.im*Real.cos h) :
    ∃ s : ℝ, s≠0 ∧ (fun j : Fin 3 => (![Real.cos h,Real.sin h,0] : Fin 3 → ℝ) j)=s • ![v.re,v.im,0] := by
  have n : v.re^2+v.im^2=1 := by
    have eq := Complex.normSq_eq_norm_sq v
    rw [unit,one_pow,Complex.normSq_apply] at eq
    simpa only [sq] using eq
  let s := Real.cos h*v.re+Real.sin h*v.im
  have x : Real.cos h=s*v.re := by dsimp [s]; linear_combination -(v.im)*parallel-(Real.cos h)*n
  have y : Real.sin h=s*v.im := by dsimp [s]; linear_combination (v.re)*parallel-(Real.sin h)*n
  have non : s≠0 := by
    intro zero
    rw [zero,zero_mul] at x y
    have z := Real.sin_sq_add_cos_sq h
    rw [x,y] at z
    norm_num at z
  exact ⟨s,non,by ext j; fin_cases j; exact x; exact y; simp⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.horizontal_line_tangent_to_ruling
