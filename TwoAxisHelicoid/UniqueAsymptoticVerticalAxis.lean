import TwoAxisHelicoid.HelicoidAsymptoticLines

namespace TwoAxisHelicoid
open Complex Matrix Set Filter
open scoped Topology
set_option maxHeartbeats 1300000

/-- An entire vertical line lying in a surface that approaches a
helicoid in positional distance must be the central line. -/
theorem vertical_line_in_helicoid_end_is_central {S : Set (Fin 3 → ℝ)}
    {α : ℝ} (hα : α ≠ 0) (h : ApproachesSetAtInfinity S (range (axisRuledHelicoid I α 0)))
    (a b : ℝ) (hline : ∀ z : ℝ, ![a,b,z] ∈ S) : a = 0 ∧ b = 0 := by
  have hall (θ : ℝ) : a*Real.sin θ = b*Real.cos θ := by
    let B : Fin 3 → ℝ := ![a,b,θ/α]
    let W : Fin 3 → ℝ := ![0,0,2*Real.pi/α]
    let p := fun n : ℕ => B+((n:ℝ)+1) • W
    have hn : W ≠ 0 := by
      intro hh
      exact (div_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hα)
        (show W 2 = 0 from congrFun hh 2)
    have hp (n : ℕ) : p n ∈ S := by
      have he : p n = ![a,b,p n 2] := by
        ext j
        fin_cases j <;> simp [p,B,W]
      rw [he]
      exact hline _
    have hphase (n : ℕ) : α*p n 2 = θ+(n+1:ℕ)*(2*Real.pi) := by
      change α*(θ/α+((n:ℝ)+1)*(2*Real.pi/α)) = _
      simp only [Nat.cast_add,Nat.cast_one]
      field_simp
    obtain ⟨q,hq,hclose⟩ := h.exists_sequence (range_nonempty _) hp (affine_ray_norm_tendsto_atTop B W hn)
    have hd (j : Fin 3) : Tendsto (fun n : ℕ => q n j-p n j) atTop (𝓝 0) :=
      (continuous_apply j).continuousAt.tendsto.comp hclose
    have hx : Tendsto (fun n : ℕ => q n 0) atTop (𝓝 a) := by
      simpa [p,B,W] using (hd 0).add (tendsto_const_nhds (x := a))
    have hy : Tendsto (fun n : ℕ => q n 1) atTop (𝓝 b) := by
      simpa [p,B,W] using (hd 1).add (tendsto_const_nhds (x := b))
    let f := fun n : ℕ => α*(q n 2-p n 2)+θ
    have hf : Tendsto f atTop (𝓝 θ) := by
      simpa [f] using ((tendsto_const_nhds (x := α)).mul (hd 2)).add (tendsto_const_nhds (x := θ))
    have heq (n : ℕ) : q n 0*Real.sin (f n) = q n 1*Real.cos (f n) := by
      have hh := normalized_helicoid_side_identity (hq n)
      have hd' : α*q n 2 = f n+(n+1:ℕ)*(2*Real.pi) := by
        dsimp only [f]
        linarith only [hphase n]
      rwa [hd',Real.sin_add_nat_mul_two_pi,Real.cos_add_nat_mul_two_pi] at hh
    exact tendsto_nhds_unique (hx.mul (Real.continuous_sin.continuousAt.tendsto.comp hf))
      ((hy.mul (Real.continuous_cos.continuousAt.tendsto.comp hf)).congr fun n => (heq n).symm)
  exact ⟨by simpa using hall (Real.pi/2),by simpa using (hall 0).symm⟩

/-- The affine Euclidean half-turn around a horizontal line through A
with unit tangent U, written as twice the line projection minus the
original displacement. -/
def horizontalLineHalfTurn (A U P : Fin 3 → ℝ) : Fin 3 → ℝ :=
  A + (2*((P-A) ⬝ᵥ U)) • U - (P-A)

/-- If the central vertical axis lies in the surface and the spatial
half-turn around a horizontal line preserves it, the two lines meet.
The proof uses the unique possible location of a vertical line. -/
theorem horizontal_half_turn_line_intersects_vertical_axis {S : Set (Fin 3 → ℝ)}
    {α : ℝ} (hα : α ≠ 0) (h : ApproachesSetAtInfinity S (range (axisRuledHelicoid I α 0)))
    (hZ : ∀ z : ℝ, ![0,0,z] ∈ S) (A U : Fin 3 → ℝ) (hu : U 2 = 0)
    (hSym : MapsTo (horizontalLineHalfTurn A U) S S) :
    ∃ t : ℝ, A+t • U = ![0,0,A 2] := by
  let s := -(A 0*U 0+A 1*U 1)
  let a := 2*(A 0+s*U 0)
  let b := 2*(A 1+s*U 1)
  have hline (z : ℝ) : ![a,b,z] ∈ S := by
    have hh := hSym (hZ (2*A 2-z))
    have hd : ((![0,0,2*A 2-z] : Fin 3 → ℝ)-A) ⬝ᵥ U = s := by
      simp [dotProduct,Fin.sum_univ_succ,hu,s]
      ring
    have he : horizontalLineHalfTurn A U ![0,0,2*A 2-z] = ![a,b,z] := by
      unfold horizontalLineHalfTurn
      rw [hd]
      ext j
      fin_cases j
      · change A 0+(2*s)*U 0-(0-A 0) = 2*(A 0+s*U 0)
        ring
      · change A 1+(2*s)*U 1-(0-A 1) = 2*(A 1+s*U 1)
        ring
      · change A 2+(2*s)*U 2-(2*A 2-z-A 2) = z
        rw [hu]
        ring
    rwa [he] at hh
  obtain ⟨ha,hb⟩ := vertical_line_in_helicoid_end_is_central hα h a b hline
  refine ⟨s,?_⟩
  ext j
  fin_cases j
  · change A 0+s*U 0=0
    dsimp only [a] at ha
    linarith
  · change A 1+s*U 1=0
    dsimp only [b] at hb
    linarith
  · change A 2+s*U 2=A 2
    simp [hu]

theorem horizontal_translation_symmetry_is_trivial {S : Set (Fin 3 → ℝ)}
    {α : ℝ} (hα : α ≠ 0) (h : ApproachesSetAtInfinity S (range (axisRuledHelicoid I α 0)))
    (hZ : ∀ z : ℝ, ![0,0,z] ∈ S) (v : Fin 3 → ℝ)
    (hT : MapsTo (fun p => p+v) S S) : v 0 = 0 ∧ v 1 = 0 := by
  apply vertical_line_in_helicoid_end_is_central hα h
  intro z
  have hh := hT (hZ (z-v 2))
  have he : (![0,0,z-v 2] : Fin 3 → ℝ)+v = ![v 0,v 1,z] := by
    ext j
    fin_cases j <;> simp
  exact he ▸ hh

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.horizontal_half_turn_line_intersects_vertical_axis
