import TwoAxisHelicoid.OriginalSurfaceSchwarz
import TwoAxisHelicoid.AntiholomorphicPunctureGerm
import TwoAxisHelicoid.ReflectedPhysicalCapExterior

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ComplexConjugate ContDiff Manifold

/-- A connected closed embedded conformal harmonic surface of arbitrary
genus, with the two complete axes and one puncture, has a genuine
helicoidal exterior as soon as its actual height and logarithmic Gauss
differentials have poles of order two in the frame of those axes. -/
theorem two_axis_double_poles_give_actual_exterior {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] [PreconnectedSpace M] {X : M → Fin 3 → ℝ}
    (embedded : IsClosedEmbedding X) (charts : ∀ d∈atlas ℂ M, HarmonicImmersionChart X d)
    (horizontal : ∀ s : ℝ, (![s,0,0] : Fin 3 → ℝ)∈range X)
    (vertical : ∀ s : ℝ, (![0,0,s] : Fin 3 → ℝ)∈range X)
    (A : GeometricDoublePoleEnd X) :
    ∃ G : GeometricExteriorCoordinate X, G.pitch≠0 ∧ G.correction 0=0 := by
  let E := A.endChart
  obtain ⟨h,ah,ih,mh⟩ := horizontal_schwarz_on_original_surface embedded charts horizontal
  obtain ⟨v,av,iv,mv⟩ := vertical_schwarz_on_original_surface embedded charts vertical
  obtain ⟨H,ha,hz,hn,hitH⟩ := antiholomorphic_involution_at_puncture E h ih
    (ah _ _ A.holomorphic A.holomorphic)
  obtain ⟨V,va,vz,vn,hitV⟩ := antiholomorphic_involution_at_puncture E v iv
    (av _ _ A.holomorphic A.holomorphic)
  let B := conj ∘ V ∘ conj
  let u := H ∘ B
  have ba : AnalyticAt ℂ B 0 := by simpa only [map_zero] using reflected_analytic_germ va
  have bz : B 0=0 := by simp only [B,Function.comp_apply,map_zero,vz]
  have bd : deriv B 0=conj (deriv V 0) := by simpa only [map_zero] using va.differentiableAt.hasDerivAt.conj_conj.deriv
  have bn : deriv B 0≠0 := bd.trans_ne (fun eq => vn (Complex.conjCLE.injective (eq.trans (map_zero conj).symm)))
  have hB : AnalyticAt ℂ H (B 0) := by rwa [bz]
  have ua : AnalyticAt ℂ u 0 := hB.comp ba
  have uz : u 0=0 := by simp only [u,Function.comp_apply,bz,hz]
  have un : deriv u 0≠0 := by
    rw [show deriv u 0=deriv H (B 0)*deriv B 0 from deriv_comp 0 hB.differentiableAt ba.differentiableAt,bz]
    exact mul_ne_zero hn bn
  have tb : Tendsto B (𝓝[≠] (0:ℂ)) (𝓝[≠] 0) := by simpa only [bz] using ba.differentiableAt.hasDerivAt.tendsto_nhdsNE bn
  have tc := conjugation_tendsto_punctured_origin
  apply geometric_exterior_of_reflected_spatial_cap charts A u H ua uz un ha hz hn
  · filter_upwards [tb.eventually hitH,tc.eventually hitV] with z hh hv
    change X (E.coord.symm (H (B z)))=halfTurnX (halfTurnZ (X (E.coord.symm z)))
    have comp : conj (B z)=V (conj z) := by simp only [B,Function.comp_apply,starRingEnd_self_apply]
    have eq : E.coord.symm (V (conj z))=v (E.coord.symm z) := by simpa only [starRingEnd_self_apply] using hv.2
    rw [hh.2,comp,eq,mh,mv]
  · filter_upwards [hitH] with z hh
    change X (E.coord.symm (H z))=halfTurnX (X (E.coord.symm (conj z)))
    rw [hh.2,mh]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.two_axis_double_poles_give_actual_exterior
