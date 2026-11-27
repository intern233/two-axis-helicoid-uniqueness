import TwoAxisHelicoid.AsymptoticSimilarityAxis
import TwoAxisHelicoid.AxisTangentIsotropy
import TwoAxisHelicoid.SimilarityHeightAndDilation
import TwoAxisHelicoid.HarmonicAtlasTangentFlow
import TwoAxisHelicoid.OriginalPositionalHelicoid

namespace TwoAxisHelicoid
open Complex Matrix Set Filter Topology InnerProductSpace
open scoped Topology ContDiff Manifold

/-- On the original positionally asymptotic embedded surface, no nonzero
infinitesimal similarity is everywhere tangent. Only an oriented harmonic
atlas and its normal formula are used. In particular an exterior
compactification or a complex torus marking is unnecessary. -/
theorem positional_similarity_velocity_kernel (s : OriginalPositionallyAsymptoticHelicoid)
    (S : ChartedSpace ℂ s.carrier) (N : s.carrier → Fin 3 → ℝ)
    (charts : ∀ e ∈ S.atlas, HarmonicImmersionChart s.position e)
    (normal : ∀ e ∈ S.atlas, ∀ z ∈ e.target, N (e.symm z)=harmonicChartNormal (s.position ∘ e.symm) z)
    (a b : Fin 3 → ℝ) (d : ℝ) (zero : ∀ p, similarityNormal s.position N a b d p=0) :
    a=0 ∧ b=0 ∧ d=0 := by
  let _ := S
  let L := similarityLinear b d
  have pres := harmonic_atlas_tangent_flow_preserves s.position N s.closedEmbedding.isClosed_range charts normal a b d zero
  obtain ⟨a₀,a₁,b₀,b₁⟩ := asymptotic_vertical_axis_similarity_velocities s.axes.pitch_ne s.approaches s.axes.vertical a b d pres
  have rigid (hd : d=0) : a 2=0 := invariant_axial_rigid_motion_translation_zero s.toOriginalSmoothHelicoid a b b₀ b₁ (hd ▸ pres)
  let h := -(a 2)/d
  let o : Fin 3 → ℝ := ![0,0,h]
  have vanish : a 2+d*h=0 := by
    by_cases hd : d=0
    · rw [hd,zero_mul,rigid hd,add_zero]
    · dsimp [h]; field_simp; ring
  have fixed : similarityField a b d o=0 := by
    funext j
    fin_cases j <;> simp [similarityField,o,cross_apply,vecHead,vecTail,a₀,a₁,b₀,b₁,vanish]
  have origin : o ∈ range s.position := s.axes.vertical h
  obtain ⟨p,hp⟩ := origin
  let e := chartAt ℂ p
  let X := s.position ∘ e.symm
  let z := e p
  have ep : p ∈ e.source := mem_chart_source ℂ p
  have em : e ∈ S.atlas := chart_mem_atlas ℂ p
  have ez : z ∈ e.target := e.map_source ep
  obtain ⟨harm,conf,imm⟩ := charts e em z ez
  have an : AnalyticAt ℝ X z := analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (harm j)
  have pos : X z=o := (congrArg s.position (e.left_inv ep)).trans hp
  let v : Fin 3 → ℝ := ![0,0,1]
  let γ := fun t : ℝ => o+t • v
  have dg : HasDerivAt γ v 0 := by simpa only [one_smul] using! ((hasDerivAt_id (0:ℝ)).smul_const v).const_add o
  have inside (t : ℝ) : γ t ∈ range s.position := by
    have val : γ t=![0,0,h+t] := by ext j; fin_cases j <;> simp [γ,o,v]
    exact val ▸ s.axes.vertical (h+t)
  have axis := embedded_chart_contains_curve_velocity s.position s.closedEmbedding.isEmbedding e ep an imm dg
    (show γ 0=s.position p by simp [γ,hp]) (Eventually.of_forall inside)
  obtain ⟨hn,_,_,_,_,unit,nx,ny⟩ := harmonicChartNormal_data an conf imm
  have orth (w : ℂ) : fderiv ℝ X z w ⬝ᵥ harmonicChartNormal X z=0 := by
    rw [dotProduct_comm,real_complex_map_columns (fderiv ℝ X z) w,dotProduct_add,dotProduct_smul,dotProduct_smul]
    change w.re*(harmonicChartNormal X z ⬝ᵥ planePartial 1 X z)+w.im*(harmonicChartNormal X z ⬝ᵥ planePartial I X z)=0
    rw [nx,ny,mul_zero,mul_zero,add_zero]
  have tangent : ∀ᶠ w in 𝓝 z, similarityField a b d (X w) ⬝ᵥ harmonicChartNormal X w=0 := by
    filter_upwards [e.open_target.mem_nhds ez] with w hw
    rw [← normal e em w hw]
    exact zero _
  have b₂ := vertical_rotation_zero_at_tangent_fixed_point an.differentiableAt hn.differentiableAt imm unit orth
    axis a b d b₀ b₁ (pos.symm ▸ fixed) tangent
  have bz : b=0 := by ext j; fin_cases j <;> assumption
  have radial (q : Fin 3 → ℝ) : a+L q=d • (q-o) := by
    have lv : L q=d • q := by simp [L,similarityLinear_apply,bz]
    have base : a=-(d • o) := by
      funext j
      fin_cases j
      · change a 0 = -(d*0); rw [a₀,mul_zero,neg_zero]
      · change a 1 = -(d*0); rw [a₁,mul_zero,neg_zero]
      · change a 2 = -(d*h); linarith only [vanish]
    rw [lv,base,smul_sub]
    abel
  have dz := invariant_radial_flow_dilation_zero s.toOriginalSmoothHelicoid L a o d radial ⟨p,hp⟩ pres
  have a₂ := rigid dz
  exact ⟨by ext j; fin_cases j <;> assumption,bz,dz⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positional_similarity_velocity_kernel
