import TwoAxisHelicoid.SaddleHamiltonianCoordinates

namespace TwoAxisHelicoid
open Complex Set Filter Topology Function
open scoped Topology ContDiff

/-- A Morse chart and its differentiable local inverse have an
injective actual differential at the center. -/
theorem saddle_chart_injective_differential {z : ℂ} (e : OpenPartialHomeomorph ℂ (ℝ×ℝ))
    (src : z∈e.source) (de : DifferentiableAt ℝ e z) (db : DifferentiableAt ℝ e.symm (e z)) :
    Injective (fderiv ℝ e z) := by
  have germ : (e.symm ∘ e) =ᶠ[𝓝 z] id := by
    filter_upwards [e.open_source.mem_nhds src] with w hw
    exact e.left_inv hw
  have eq := (fderiv_comp z db de).symm.trans (germ.fderiv_eq.trans fderiv_id)
  intro u v same
  have lift := congrArg (fderiv ℝ e.symm (e z)) same
  calc u=((fderiv ℝ e.symm (e z)).comp (fderiv ℝ e z)) u := by rw [eq]; rfl
       _=((fderiv ℝ e.symm (e z)).comp (fderiv ℝ e z)) v := lift
       _=v := by rw [eq]; rfl

/-- The linear change from an indefinite signed square difference to
a product retains both differentiability and the nonsingular Jacobian
in the original plane coordinates. -/
theorem regular_saddle_difference_to_product {q : ℂ → ℝ×ℝ} {z : ℂ} {a : ℝ} (nz : a≠0)
    (smooth : ContDiffAt ℝ 1 q z) (inj : Injective (fderiv ℝ q z)) :
    let k := fun w => ((q w).1-(q w).2,a*((q w).1+(q w).2))
    ContDiffAt ℝ 1 k z ∧ Injective (fderiv ℝ k z) := by
  let A := fderiv ℝ q z
  let k := fun w => ((q w).1-(q w).2,a*((q w).1+(q w).2))
  have d := (smooth.differentiableAt one_ne_zero).hasFDerivAt
  have du := hasFDerivAt_fst.comp z d
  have dv := hasFDerivAt_snd.comp z d
  have dk := (du.sub dv).prodMk ((du.add dv).const_mul a)
  refine ⟨(smooth.fst.sub smooth.snd).prodMk (contDiffAt_const.mul (smooth.fst.add smooth.snd)),?_⟩
  intro x y same
  change fderiv ℝ k z x=fderiv ℝ k z y at same
  rw [show fderiv ℝ k z=_ from dk.fderiv] at same
  have xeq := congrArg Prod.fst same
  have yeq := congrArg Prod.snd same
  change (A x).1-(A x).2=(A y).1-(A y).2 at xeq
  change a*((A x).1+(A x).2)=a*((A y).1+(A y).2) at yeq
  have sum := mul_left_cancel₀ nz yeq
  apply inj
  exact Prod.ext (by linarith) (by linarith)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.saddle_chart_injective_differential
#print axioms TwoAxisHelicoid.regular_saddle_difference_to_product
