import TwoAxisHelicoid.CertifiedSaddleHeightBracket

namespace TwoAxisHelicoid
open Complex Set

/-- The fixed physical height is strictly ordered on every row of the
closed quarter. On each lower half-row its zero lies between one half
and the positive saddle, including the central half-period itself. -/
theorem certified_quarter_height_row_order :
    let p := certifiedClosedParameters
    let H := actualComplexHeight p.t p.a 1 p.height_pos
    (∀ y∈Ioo (0:ℝ) p.t, StrictMonoOn (fun x : ℝ => (H ⟨x,y⟩).re) (Icc 0 1)) ∧
    ∀ y∈Ioc (0:ℝ) (p.t/2), ∃ x∈Icc (1/2:ℝ) p.a, (H ⟨x,y⟩).re=0 := by
  intro p H
  let X := actualGlobalImmersion p.t p.a 1 p.height_pos
  let Z := fun x y : ℝ => (x:ℂ)+I*y
  have d : HasTwoAxisHelicoidCoordinateDifferential X p.t p.a 1 p.height_pos := fun z hz =>
    ((actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
      p.vertical_closed p.horizontal_closed).2.2.2 z hz).1
  have val {x y : ℝ} (hy : y∈Ioo 0 p.t) : X (Z x y) 2-X 1 2=(H ⟨x,y⟩).re := by
    have eq : Z x y=⟨x,y⟩ := by apply Complex.ext <;> simp [Z]
    have off : Z x y∉certifiedPeriodPair.lattice := rhombic_horizontal_strip_not_mem p.height_pos
      (by change (Z x y).im∈Ioo 0 p.t; rw [eq]; exact hy)
    exact (actual_complex_height_centered_primitive p.height_pos d off).trans (congrArg (fun z => (H z).re) eq)
  refine ⟨?_,?_⟩
  · intro y hy x hx w hw order
    change (H ⟨x,y⟩).re<(H ⟨w,y⟩).re
    rw [← val hy,← val hy]
    exact sub_lt_sub_right (actual_quarter_height_row_strictMono p.height_pos hy d hx hw order) _
  · intro y hy
    obtain ⟨mid,_,bracket⟩ := certified_saddle_height_bracket
    rcases hy.2.lt_or_eq with lt|eq
    · obtain ⟨x,⟨hx,hit⟩,_⟩ := bracket y ⟨hy.1,lt⟩
      have inside : y∈Ioo 0 p.t := ⟨hy.1,lt.trans (half_lt_self p.height_pos)⟩
      refine ⟨x,Ioo_subset_Icc_self hx,?_⟩
      rw [← val inside,show X (Z x y) 2=X 1 2 from hit,sub_self]
    · subst y
      have lo := (by norm_num [rootALower] : (1/2:ℝ)<rootALower).trans certifiedClosedParameters_bounds.2.1
      refine ⟨1/2,⟨le_rfl,lo.le⟩,?_⟩
      have point : (⟨1/2,p.t/2⟩:ℂ)=(1+I*p.t)/2 := by apply Complex.ext <;> simp
      rw [point]
      exact mid

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_quarter_height_row_order
