import TwoAxisHelicoid.OriginalExteriorTorusReduction
import TwoAxisHelicoid.ExteriorHeightCompactCore

namespace TwoAxisHelicoid
open Complex Set Filter Bornology Topology
open scoped Topology ContDiff Manifold

/-- Normalize the Gauss correction to vanish at the added point by
translating the actual height chart, then taking a smaller round
exterior. This retains the same spatial immersion and the same pitch. -/
theorem GeometricExteriorCoordinate.normalized {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    {X : M → Fin 3 → ℝ} (A : GeometricExteriorCoordinate X) (cx : Continuous X) (tails : HasConnectedCompactTails M) :
    ∃ D : GeometricExteriorCoordinate X, D.pitch=A.pitch ∧ D.correction 0=0 := by
  let e := A.chart
  let k := I*(A.pitch:ℂ)
  have kn : k≠0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr A.pitch_ne)
  let c := -(A.correction 0)/k
  let R := A.radius+‖c‖+1
  let S := {w : ℂ | R<‖w‖}
  have op : IsOpen S := isOpen_lt continuous_const continuous_norm
  let tr := (Homeomorph.addRight c).symm.toOpenPartialHomeomorph
  let d := (e.trans tr).trans (OpenPartialHomeomorph.ofSet S op)
  have fw (x : M) : d x=e x-c := rfl
  have bw (w : ℂ) : d.symm w=e.symm (w+c) := rfl
  have old {w : ℂ} (large : w∈S) : w+c∈e.target := by
    rw [show e.target=_ from A.target]
    have le : ‖w‖≤‖w+c‖+‖c‖ := by simpa only [add_sub_cancel_right] using norm_sub_le (w+c) c
    change A.radius+‖c‖+1<‖w‖ at large
    change A.radius<‖w+c‖
    linarith
  have target : d.target=S := by
    ext w
    change w∈S ∧ (w∈univ ∧ w+c∈e.target) ↔ w∈S
    exact ⟨And.left,fun h => ⟨h,mem_univ _,old h⟩⟩
  have esc := true_exterior_height_coordinate_escapes tails e A.target A.core _ ((continuous_apply 2).comp cx) A.heightOffset A.height
  have mem : d.source∈cocompact M := by
    have s : e.source∈cocompact M := by simpa only [compl_compl] using A.core.compl_mem_cocompact
    filter_upwards [s,esc.eventually_gt_atTop (R+‖c‖)] with x hx far
    refine ⟨⟨hx,mem_univ _⟩,?_⟩
    change R<‖e x-c‖
    have bound := norm_add_le (e x-c) c
    rw [sub_add_cancel] at bound
    linarith
  obtain ⟨K,compact,sub⟩ := mem_cocompact.mp mem
  have core : IsCompact d.sourceᶜ := compact.of_isClosed_subset d.open_source.isClosed_compl (fun x hx => by by_contra h; exact hx (sub h))
  have hol : d∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M := by
    apply d.mem_maximalAtlas_of_contMDiffOn
    · intro x hx
      exact ((contMDiffAt_of_mem_maximalAtlas A.holomorphic hx.1.1).sub contMDiffAt_const).contMDiffWithinAt
    · intro w hw
      have h := old (show w∈S by rwa [← target])
      exact ((contMDiffAt_symm_of_mem_maximalAtlas A.holomorphic h).comp w (contMDiffAt_id.add contMDiffAt_const)).contMDiffWithinAt
  let u := fun w : ℂ => w/(1+c*w)
  let f := fun w => A.correction (u w)-A.correction 0
  have hu : AnalyticAt ℂ u 0 := analyticAt_id.div (analyticAt_const.add (analyticAt_const.mul analyticAt_id)) (by simp)
  have u0 : u 0=0 := by simp [u]
  have fa : AnalyticAt ℂ f 0 := (A.analytic.comp_of_eq hu u0).sub analyticAt_const
  have fp : 0<R := by dsimp [R]; linarith [A.positive,norm_nonneg c]
  refine ⟨⟨d,R,fp,target,core,hol,A.heightOffset+c.re,?_,A.pitch,A.pitch_ne,f,fa,?_⟩,rfl,by simp [f,u0]⟩
  · intro x hx
    rw [A.height x hx.1.1,fw,Complex.sub_re]
    ring
  · have shift : Tendsto (fun w : ℂ => w+c) (cobounded ℂ) (cobounded ℂ) := by
      apply tendsto_norm_atTop_iff_cobounded.mp
      apply Filter.tendsto_atTop.mpr
      intro r
      filter_upwards [tendsto_norm_cobounded_atTop.eventually_ge_atTop (r+‖c‖)] with z h
      have b : ‖z‖≤‖z+c‖+‖c‖ := by simpa only [add_sub_cancel_right] using norm_sub_le (z+c) c
      linarith
    filter_upwards [shift.eventually A.gauss,tendsto_norm_cobounded_atTop.eventually_gt_atTop 0] with z h n
    have coeff : immersionComplexCoefficient (X ∘ d.symm) z=immersionComplexCoefficient (X ∘ e.symm) (z+c) := by
      funext l
      have ev := fderiv_comp_add_right (𝕜 := ℝ) (f := fun w => X (e.symm w) l) (x := z) c
      unfold immersionComplexCoefficient scalarComplexCoefficient
      change _=_
      simp only [Function.comp_apply,bw,ev]
    change nullGauss (immersionComplexCoefficient (X ∘ d.symm) z)=exp (k*z+f z⁻¹)
    rw [coeff,show nullGauss (immersionComplexCoefficient (X ∘ e.symm) (z+c))=_ from h]
    have nz := norm_pos_iff.mp n
    have inv : u z⁻¹=(z+c)⁻¹ := by
      dsimp [u]
      rw [show 1+c*z⁻¹=(z+c)/z by field_simp,div_div_eq_mul_div,inv_mul_cancel₀ nz,one_div]
    dsimp only [f]
    rw [inv,show I*(A.pitch:ℂ)*(z+c)=k*z+k*c from mul_add _ _ _,show k*c= -(A.correction 0) by dsimp [c]; field_simp]
    congr 1
    ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.GeometricExteriorCoordinate.normalized
