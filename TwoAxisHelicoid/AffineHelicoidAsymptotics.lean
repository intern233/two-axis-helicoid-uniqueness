import TwoAxisHelicoid.HelicoidAsymptoticContainment

namespace TwoAxisHelicoid
open Set Filter Topology

/-- A continuous linear change of Euclidean coordinates followed by translation
preserves the one-sided positional asymptote at infinity, even when the
coordinate model uses a norm not fixed by the ambient rotation. -/
theorem ApproachesSetAtInfinity.affine_image {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S T : Set E} (h : ApproachesSetAtInfinity S T) (L : E →L[ℝ] F) (P : F) :
    ApproachesSetAtInfinity ((fun x => P+L x) '' S) ((fun x => P+L x) '' T) := by
  intro ε hε
  let K := ‖L‖+1
  have hK : 0 < K := by dsimp [K]; positivity
  have hKL : ‖L‖ ≤ K := by dsimp [K]; linarith
  obtain ⟨B,hB⟩ := h (ε/K) (div_pos hε hK)
  refine ⟨‖P‖+K*B,?_⟩
  rintro _ ⟨x,hx,rfl⟩ hab
  have ht : ‖P+L x‖ ≤ ‖P‖+K*‖x‖ := (norm_add_le _ _).trans (add_le_add_right
    ((L.le_opNorm x).trans (mul_le_mul_of_nonneg_right hKL (norm_nonneg x))) _)
  have hnx : B ≤ ‖x‖ := (mul_le_mul_iff_right₀ hK).mp (le_of_add_le_add_left (hab.trans ht))
  obtain ⟨y,hy,hxy⟩ := hB x hx hnx
  refine ⟨P+L y,mem_image_of_mem _ hy,?_⟩
  rw [dist_add_left,dist_eq_norm,← map_sub]
  have hbound := (L.le_opNorm (x-y)).trans (mul_le_mul_of_nonneg_right hKL (norm_nonneg _))
  exact hbound.trans_lt (by simpa only [mul_comm K,← dist_eq_norm] using (lt_div_iff₀ hK).mp hxy)

/-- Invertible affine Euclidean placements carry spatial asymptotes in both
directions. -/
theorem ApproachesSetAtInfinity.affine_equiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S T : Set E) (L : E ≃L[ℝ] F) (P : F) :
    ApproachesSetAtInfinity ((fun x => P+L x) '' S) ((fun x => P+L x) '' T) ↔
      ApproachesSetAtInfinity S T := by
  refine ⟨fun h => ?_,fun h => h.affine_image L.toContinuousLinearMap P⟩
  have h' := h.affine_image L.symm.toContinuousLinearMap (-L.symm P)
  have hset (U : Set E) : (fun y => -L.symm P + L.symm y) '' ((fun x => P+L x) '' U) = U := by
    rw [image_image]
    have he : (fun x : E => -L.symm P+L.symm (P+L x)) = id := by ext x; simp
    rw [he,image_id]
  change ApproachesSetAtInfinity ((fun y => -L.symm P+L.symm y) '' _) ((fun y => -L.symm P+L.symm y) '' _) at h'
  rwa [hset,hset] at h'

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.ApproachesSetAtInfinity.affine_equiv
