import TwoAxisHelicoid.HelicoidGroundState
import TwoAxisHelicoid.VectorBivariateDerivative
import TwoAxisHelicoid.HelicoidTubeMetric

namespace TwoAxisHelicoid
open Real

noncomputable def logGaussSphere (u v : ℝ) : Fin 3 → ℝ :=
  ![cos v/cosh u,sin v/cosh u,sinh u/cosh u]

noncomputable def logGaussSphereU (u v : ℝ) : Fin 3 → ℝ :=
  ![-cos v*sinh u/(cosh u)^2,-sin v*sinh u/(cosh u)^2,1/(cosh u)^2]

noncomputable def logGaussSphereV (u v : ℝ) : Fin 3 → ℝ :=
  ![-sin v/cosh u,cos v/cosh u,0]

theorem logGaussSphere_unit (u v : ℝ) :
    (∑ j, (logGaussSphere u v j)^2) = 1 := by
  simp only [Fin.sum_univ_succ,logGaussSphere,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Fin.sum_univ_zero]
  field_simp [(cosh_pos u).ne']
  nlinarith [sin_sq_add_cos_sq v,cosh_sq_sub_sinh_sq u]

theorem logGaussSphere_frame_metric (u v : ℝ) :
    (∑ j, (logGaussSphereU u v j)^2) = 1/(cosh u)^2 ∧
    (∑ j, (logGaussSphereV u v j)^2) = 1/(cosh u)^2 ∧
    (∑ j, logGaussSphereU u v j*logGaussSphereV u v j) = 0 := by
  simp only [Fin.sum_univ_succ,logGaussSphereU,logGaussSphereV,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero]
  constructor
  · field_simp [(cosh_pos u).ne']
    nlinarith [cosh_sq_sub_sinh_sq u,
      congrArg (fun x : ℝ => (sinh u)^2*x) (sin_sq_add_cos_sq v)]
  constructor
  · field_simp [(cosh_pos u).ne']
    nlinarith [sin_sq_add_cos_sq v]
  · ring

theorem logGaussSphereU_hasDerivAt (u v : ℝ) :
    HasDerivAt (fun x => logGaussSphere x v) (logGaussSphereU u v) u := by
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases j <;> dsimp [logGaussSphere,logGaussSphereU]
  · convert (hasDerivAt_const u (cos v)).div (hasDerivAt_cosh u) (cosh_pos u).ne' using 1
    ring
  · convert (hasDerivAt_const u (sin v)).div (hasDerivAt_cosh u) (cosh_pos u).ne' using 1
    ring
  · convert real_tanh_hasDerivAt u using 1
    funext x
    exact (tanh_eq_sinh_div_cosh x).symm

theorem logGaussSphereV_hasDerivAt (u v : ℝ) :
    HasDerivAt (logGaussSphere u) (logGaussSphereV u v) v := by
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases j <;> dsimp [logGaussSphere,logGaussSphereV]
  · exact (hasDerivAt_cos v).div_const (cosh u)
  · exact (hasDerivAt_sin v).div_const (cosh u)
  · exact hasDerivAt_const v _

theorem logGaussSphere_curve_hasDerivAt {u v : ℝ → ℝ} {a b t : ℝ}
    (hu : HasDerivAt u a t) (hv : HasDerivAt v b t) :
    HasDerivAt (fun s => logGaussSphere (u s) (v s))
      (a • logGaussSphereU (u t) (v t)+b • logGaussSphereV (u t) (v t)) t := by
  apply vector_bivariate_curve_hasDerivAt (F := logGaussSphere)
    (Ft := logGaussSphereU) (Fa := logGaussSphereV)
    (Filter.Eventually.of_forall (fun p => logGaussSphereU_hasDerivAt p.1 p.2))
    (Filter.Eventually.of_forall (fun p => logGaussSphereV_hasDerivAt p.1 p.2)) _ _ hu hv
  · apply Continuous.continuousAt
    apply continuous_pi
    intro j
    fin_cases j <;> dsimp [logGaussSphereU] <;> fun_prop (disch := intros; positivity)
  · apply Continuous.continuousAt
    apply continuous_pi
    intro j
    fin_cases j <;> dsimp [logGaussSphereV] <;> fun_prop (disch := intros; positivity)

theorem logGaussSphere_combination_energy (u v a b : ℝ) :
    (∑ j, (a*logGaussSphereU u v j+b*logGaussSphereV u v j)^2) =
      (a^2+b^2)/(cosh u)^2 := by
  obtain ⟨hU,hV,hUV⟩ := logGaussSphere_frame_metric u v
  have h := sum_sq_three_vectors (logGaussSphereU u v) (logGaussSphereV u v)
    (0 : Fin 3 → ℝ) a b 0
  simpa [hU,hV,hUV,div_eq_mul_inv,add_mul] using h

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.logGaussSphere_combination_energy
