import TwoAxisHelicoid.WholePlaneWeakCorrector

namespace TwoAxisHelicoid
open MeasureTheory Complex Set Filter InnerProductSpace
open scoped ContDiff RealInnerProductSpace

noncomputable def planeFieldTranslate (t : ℂ) : Lp ℂ 2 (volume:Measure ℂ) →ₗᵢ[ℝ] Lp ℂ 2 (volume:Measure ℂ) :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun z => z+t) (measurePreserving_add_right volume t)

theorem planeFieldTranslate_ae (t : ℂ) (w : Lp ℂ 2 (volume:Measure ℂ)) :
    ⇑(planeFieldTranslate t w) =ᵐ[volume] (fun z => w (z+t)) :=
  Lp.coeFn_compMeasurePreserving w (measurePreserving_add_right volume t)

/-- Ordinary translations preserve the L² closure of genuine compact test gradients. -/
theorem planeFieldTranslate_mem_gradients (t : ℂ) {w : Lp ℂ 2 (volume:Measure ℂ)}
    (hw : w∈planeDirichletGradients volume univ) :
    planeFieldTranslate t w∈planeDirichletGradients volume univ := by
  let S := planeDirichletGradients volume univ
  let τ := planeFieldTranslate t
  have closed : IsClosed (S : Set (Lp ℂ 2 (volume:Measure ℂ))) := Submodule.isClosed_topologicalClosure _
  have inc : S ≤ S.comap τ.toLinearMap := by
    apply Submodule.topologicalClosure_minimal _ _ (closed.preimage τ.continuous)
    apply Submodule.span_le.mpr
    rintro v ⟨φ,s,h,_,hv⟩
    change τ v∈S
    apply Submodule.le_topologicalClosure _
    apply Submodule.subset_span
    let ψ := fun z => φ (z+t)
    have compact : HasCompactSupport ψ := by
      apply HasCompactSupport.of_support_subset_isCompact ((Homeomorph.addRight t).isCompact_preimage.mpr h)
      exact fun z hz => subset_tsupport φ (show φ (z+t)≠0 from hz)
    refine ⟨ψ,s.comp (contDiff_id.add contDiff_const),compact,subset_univ _,?_⟩
    have shift := (measurePreserving_add_right volume t).quasiMeasurePreserving.ae_eq_comp hv
    filter_upwards [planeFieldTranslate_ae t v,shift] with z hz hy
    change τ v z=planeTestGradient ψ z
    change v (z+t)=planeTestGradient φ (z+t) at hy
    rw [hz,hy]
    apply Complex.ext <;> simp only [planeTestGradient,ψ,fderiv_comp_add_right]
  exact inc hw

theorem planeFieldTranslate_cancel (t : ℂ) (w : Lp ℂ 2 (volume:Measure ℂ)) :
    planeFieldTranslate t (planeFieldTranslate (-t) w)=w := by
  apply Lp.ext
  have shift := (measurePreserving_add_right volume t).quasiMeasurePreserving.ae_eq_comp (planeFieldTranslate_ae (-t) w)
  filter_upwards [planeFieldTranslate_ae t (planeFieldTranslate (-t) w),shift] with z hz hy
  change planeFieldTranslate (-t) w (z+t)=w (z+t+-t) at hy
  exact hz.trans (hy.trans (congrArg (fun y => w y) (by abel)))

theorem planeFieldTranslate_preserves_zero_flux (t : ℂ) (q : Lp ℂ 2 (volume:Measure ℂ))
    (hq : ∀ w ∈ planeDirichletGradients volume univ, ⟪q,w⟫_ℝ=0) :
    ∀ w ∈ planeDirichletGradients volume univ, ⟪planeFieldTranslate t q,w⟫_ℝ=0 := by
  intro w hw
  have id := (planeFieldTranslate t).inner_map_map q (planeFieldTranslate (-t) w)
  rw [planeFieldTranslate_cancel,hq _ (planeFieldTranslate_mem_gradients (-t) hw)] at id
  exact id

/-- Testing the translated and original equations against the difference of the
two gradients controls its L² norm by the load and conductivity increments. -/
theorem whole_plane_gradient_translation_energy
    (T : Lp ℂ 2 (volume:Measure ℂ) →L[ℝ] Lp ℂ 2 (volume:Measure ℂ)) {c : ℝ}
    (lower : ∀ v, c*‖v‖^2≤⟪T v,v⟫_ℝ) (u b : Lp ℂ 2 (volume:Measure ℂ))
    (hu : u∈planeDirichletGradients volume univ)
    (sol : ∀ w∈planeDirichletGradients volume univ, ⟪T u-b,w⟫_ℝ=0) (t : ℂ) :
    c*‖planeFieldTranslate t u-u‖ ≤
      ‖T (planeFieldTranslate t u)-planeFieldTranslate t (T u)‖+‖planeFieldTranslate t b-b‖ := by
  let τ := planeFieldTranslate t
  let w := τ u-u
  have hw : w∈planeDirichletGradients volume univ := Submodule.sub_mem _ (planeFieldTranslate_mem_gradients t hu) hu
  have eq1 := sol w hw
  have eq2 := planeFieldTranslate_preserves_zero_flux t _ sol w hw
  change ⟪τ (T u-b),w⟫_ℝ=0 at eq2
  rw [map_sub,inner_sub_left] at eq2
  rw [inner_sub_left] at eq1
  have id : ⟪T w,w⟫_ℝ=⟪(T (τ u)-τ (T u))+(τ b-b),w⟫_ℝ := by
    change ⟪T (τ u-u),w⟫_ℝ=_
    rw [map_sub,inner_sub_left,inner_add_left,inner_sub_left,inner_sub_left]
    linarith
  by_cases zero : ‖w‖=0
  · change c*‖w‖≤_
    rw [zero,mul_zero]
    positivity
  have pos := lt_of_le_of_ne (norm_nonneg w) (Ne.symm zero)
  have est := (lower w).trans (id.le.trans (real_inner_le_norm _ _))
  have bound := est.trans (mul_le_mul_of_nonneg_right (norm_add_le _ _) (norm_nonneg w))
  apply (mul_le_mul_iff_left₀ pos).mp
  simpa only [w,pow_two,mul_assoc] using bound
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.planeFieldTranslate_mem_gradients
#print axioms TwoAxisHelicoid.whole_plane_gradient_translation_energy
