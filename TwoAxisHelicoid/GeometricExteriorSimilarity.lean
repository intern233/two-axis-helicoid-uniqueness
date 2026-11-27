import TwoAxisHelicoid.NormalizedGeometricExteriorCoordinate
import TwoAxisHelicoid.GaussFromVerticalRotation
import TwoAxisHelicoid.HolomorphicImmersionCoordinateChange

namespace TwoAxisHelicoid
open Complex Set Filter Bornology Topology
open scoped Topology ContDiff Manifold

private theorem spatial_coefficient_real_scale (k : ℝ) (X : ℂ → Fin 3 → ℝ) (z : ℂ) (j : Fin 3) :
    immersionComplexCoefficient (fun w => k • X w) z j = (k:ℂ)*immersionComplexCoefficient X z j := by
  let f := fun w => X w j
  change (fderiv ℝ (k • f) z 1:ℂ)-I*(fderiv ℝ (k • f) z I:ℂ)=
    (k:ℂ)*((fderiv ℝ f z 1:ℂ)-I*(fderiv ℝ f z I:ℂ))
  rw [fderiv_const_smul_field]
  change ((k*fderiv ℝ f z 1:ℝ):ℂ)-I*((k*fderiv ℝ f z I:ℝ):ℂ)=_
  push_cast
  ring

/-- Transport a true exterior height chart through a spatial dilation.
The same dilation of the complex coordinate cancels the factor in the
coordinate forms, so the pitch is divided by the spatial scale. -/
theorem GeometricExteriorCoordinate.scaled {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {X : M → Fin 3 → ℝ} (A : GeometricExteriorCoordinate X)
    (reg : ∀ᶠ w in cobounded ℂ, DifferentiableAt ℝ (X ∘ A.chart.symm) w) {k : ℝ} (kn : k≠0) :
    ∃ B : GeometricExteriorCoordinate (fun x => k • X x), B.pitch=A.pitch/k ∧ B.correction 0=A.correction 0 := by
  let c : ℂ := k
  have cn : c≠0 := ofReal_ne_zero.mpr kn
  let T := Homeomorph.mulLeft₀ c cn
  let e := A.chart.trans T.toOpenPartialHomeomorph
  have source : e.source=A.chart.source := by ext x; exact ⟨fun h => h.1,fun h => ⟨h,trivial⟩⟩
  have target : e.target={w : ℂ | |k| *A.radius<‖w‖} := by
    ext w
    change (w∈univ ∧ c⁻¹*w∈A.chart.target) ↔ _
    rw [A.target]
    change (True ∧ A.radius<‖c⁻¹*w‖) ↔ |k| *A.radius<‖w‖
    rw [true_and,norm_mul,norm_inv,show ‖c‖=|k| from norm_real _,← div_eq_inv_mul,lt_div_iff₀ (abs_pos.mpr kn),mul_comm A.radius |k|]
  have chart : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M := by
    apply e.mem_maximalAtlas_of_contMDiffOn
    · intro x hx
      exact (contMDiffAt_const.mul (contMDiffAt_of_mem_maximalAtlas A.holomorphic hx.1)).contMDiffWithinAt
    · intro w hw
      exact ((contMDiffAt_symm_of_mem_maximalAtlas A.holomorphic hw.2).comp w (contMDiffAt_const.mul contMDiffAt_id)).contMDiffWithinAt
  let g := fun w => A.correction (c*w)
  have an : AnalyticAt ℂ g 0 := A.analytic.comp_of_eq (analyticAt_const.mul analyticAt_id) (mul_zero _)
  have esc : Tendsto (fun w : ℂ => c⁻¹*w) (cobounded ℂ) (cobounded ℂ) := by
    apply tendsto_norm_atTop_iff_cobounded.mp
    simpa only [norm_mul] using (tendsto_norm_cobounded_atTop (E := ℂ)).const_mul_atTop (norm_pos_iff.mpr (inv_ne_zero cn))
  refine ⟨⟨e,|k| *A.radius,mul_pos (abs_pos.mpr kn) A.positive,target,by rw [source]; exact A.core,chart,k*A.heightOffset,?_,
    A.pitch/k,div_ne_zero A.pitch_ne kn,g,an,?_⟩,rfl,by simp [g]⟩
  · intro x hx
    change k*X x 2=k*A.heightOffset+(c*A.chart x).re
    rw [A.height x hx.1]
    simp [c,Complex.mul_re,mul_add]
  · filter_upwards [esc.eventually reg,esc.eventually A.gauss] with w diff gauss
    let Y := X ∘ A.chart.symm
    let S := fun z : ℂ => c⁻¹*z
    have der : HasDerivAt S c⁻¹ w := by simpa only [S,id_eq,mul_one] using (hasDerivAt_id w).const_mul c⁻¹
    have eq : immersionComplexCoefficient ((fun x => k • X x) ∘ e.symm) w=immersionComplexCoefficient Y (S w) := by
      funext j
      change immersionComplexCoefficient (fun z => k • (Y ∘ S) z) w j=_
      rw [spatial_coefficient_real_scale,immersionComplexCoefficient_comp_holomorphic diff der,← mul_assoc]
      change (c*c⁻¹)*_=_
      rw [mul_inv_cancel₀ cn,one_mul]
    change nullGauss (immersionComplexCoefficient _ w)=_
    rw [eq,show nullGauss (immersionComplexCoefficient Y (S w))=_ from gauss]
    congr 1
    change I*(A.pitch:ℂ)*(c⁻¹*w)+A.correction (c⁻¹*w)⁻¹=I*((A.pitch/k:ℝ):ℂ)*w+A.correction (c*w⁻¹)
    rw [_root_.mul_inv_rev,inv_inv,mul_comm w⁻¹ c,ofReal_div]
    dsimp [c]
    ring

/-- Rotation about the vertical axis leaves the height chart fixed and
adds the constant logarithm of the rotation to its Gauss correction. -/
theorem GeometricExteriorCoordinate.rotated {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    {X : M → Fin 3 → ℝ} (A : GeometricExteriorCoordinate X) (reg : ∀ᶠ w in cobounded ℂ, DifferentiableAt ℝ (X ∘ A.chart.symm) w)
    {q : ℂ} (unit : ‖q‖=1) :
    ∃ B : GeometricExteriorCoordinate (verticalRotation q ∘ X), B.pitch=A.pitch := by
  have nz : q≠0 := fun h => by simp [h] at unit
  refine ⟨⟨A.chart,A.radius,A.positive,A.target,A.core,A.holomorphic,A.heightOffset,?_,A.pitch,A.pitch_ne,
    fun z => log q+A.correction z,analyticAt_const.add A.analytic,?_⟩,rfl⟩
  · intro x hx
    exact A.height x hx
  · filter_upwards [reg,A.gauss] with w diff h
    let Y := X ∘ A.chart.symm
    have d := (verticalRotation q).hasFDerivAt.comp w (immersionComplexCoefficient_hasFDerivAt diff)
    have d' := immersionComplexCoefficient_hasFDerivAt d.differentiableAt
    have eq := nullGauss_of_rotated_real_derivative unit (d'.unique d)
    change nullGauss (immersionComplexCoefficient (verticalRotation q ∘ Y) w)=_
    rw [eq,show nullGauss (immersionComplexCoefficient Y w)=_ from h,
      show I*(A.pitch:ℂ)*w+(log q+A.correction w⁻¹)=log q+(I*(A.pitch:ℂ)*w+A.correction w⁻¹) by ring, exp_add (log q),exp_log nz]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.GeometricExteriorCoordinate.scaled
#print axioms TwoAxisHelicoid.GeometricExteriorCoordinate.rotated
