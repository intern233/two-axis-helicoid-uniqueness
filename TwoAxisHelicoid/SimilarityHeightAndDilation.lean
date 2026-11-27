import TwoAxisHelicoid.SimilarityFlowMetric
import TwoAxisHelicoid.EmbeddedAmbientFlow
import TwoAxisHelicoid.OriginalSurfaceNonperiodicity
import TwoAxisHelicoid.OriginalHandleTopology
import Mathlib.Analysis.Convex.Contractible

namespace TwoAxisHelicoid
open Complex Set Filter Topology Matrix
open scoped Topology

/-- A height drift in an image-preserving affine flow is impossible
on the embedded punctured torus, even when combined with rotations
around the vertical direction. -/
theorem invariant_axial_rigid_motion_translation_zero (s : OriginalSmoothHelicoid) (a b : Fin 3 → ℝ)
    (b₀ : b 0=0) (b₁ : b 1=0)
    (pres : ∀ t : ℝ, MapsTo (affineAmbientFlow (similarityLinear b 0) a t) (range s.position) (range s.position)) :
    a 2=0 := by
  let L := similarityLinear b 0
  let O := affineAmbientFlow L a
  have move (p : Fin 3 → ℝ) (t : ℝ) : O t p 2=p 2+t*a 2 := by
    let h := fun r : ℝ => O r p 2-r*a 2
    have hd (r : ℝ) : HasDerivAt (fun v : ℝ => O v p 2) (a 2) r := by
      have der := (ContinuousLinearMap.proj 2 : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt r
        (affineAmbientFlow_deriv L a p r)
      change HasDerivAt (fun v : ℝ => O v p 2) (a 2+(L (O r p)) 2) r at der
      have vl : (L (O r p)) 2=0 := by simp [L,similarityLinear_apply,cross_apply,b₀,b₁]
      rwa [vl,add_zero] at der
    have dh (r : ℝ) : HasDerivAt h 0 r := by
      simpa only [one_mul,sub_self] using! (hd r).sub ((hasDerivAt_id r).mul_const (a 2))
    have eq := is_const_of_deriv_eq_zero (fun r => (dh r).differentiableAt) (fun r => (dh r).deriv) t 0
    change O t p 2-t*a 2=O 0 p 2-0*a 2 at eq
    rw [show O 0 p=p from affineAmbientFlow_zero L a p,zero_mul,sub_zero] at eq
    linarith
  obtain ⟨g,hg,_,_,_,_⟩ := embedded_ambient_flow_action s.closedEmbedding.isEmbedding L a
    (fun t p => pres t (mem_range_self p))
  by_contra nz
  let e := (s.topologicalType.symm.trans (g 1)).trans s.topologicalType
  let h := fun q => s.position (s.topologicalType.symm q) 2
  apply punctured_torus_no_height_translating_homeomorphism s.modelTorus e h
    ((continuous_apply 2).comp (s.closedEmbedding.continuous.comp s.topologicalType.symm.continuous)) nz
  intro q
  change s.position (s.topologicalType.symm (s.topologicalType (g 1 (s.topologicalType.symm q)))) 2=h q+a 2
  rw [s.topologicalType.symm_apply_apply,hg]
  simpa only [one_mul] using move (s.position (s.topologicalType.symm q)) 1

/-- Exact position of the flow when the affine field is a dilation
centered at o. The exponential factor is obtained by differentiating
the rescaled displacement. -/
theorem affine_radial_flow_position {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (L : E →L[ℝ] E) (a o : E) (d : ℝ) (radial : ∀ p : E, a+L p=d • (p-o)) (p : E) (t : ℝ) :
    affineAmbientFlow L a t p=o+Real.exp (d*t) • (p-o) := by
  let X := fun r => affineAmbientFlow L a r p
  let F := fun r => Real.exp (-d*r) • (X r-o)
  have dF (r : ℝ) : HasDerivAt F 0 r := by
    have h := (((hasDerivAt_id r).const_mul (-d)).exp).smul ((affineAmbientFlow_deriv L a p r).sub_const o)
    rw [radial] at h
    change HasDerivAt F (Real.exp (-d*r) • (d • (X r-o))+(Real.exp (-d*r)*(-d*1)) • (X r-o)) r at h
    rw [smul_smul,← add_smul] at h
    simpa using h
  have eq := is_const_of_deriv_eq_zero (fun r => (dF r).differentiableAt) (fun r => (dF r).deriv) t 0
  change Real.exp (-d*t) • (X t-o)=Real.exp (-d*0) • (X 0-o) at eq
  rw [show X 0=p from affineAmbientFlow_zero L a p,mul_zero,Real.exp_zero,one_smul,neg_mul,Real.exp_neg] at eq
  have pos : Real.exp (d*t) ≠ 0 := (Real.exp_pos _).ne'
  have inv := congrArg (fun v : E => Real.exp (d*t) • v) eq
  simp only [smul_smul,mul_inv_cancel₀ pos,one_smul] at inv
  exact (sub_eq_iff_eq_add.mp inv).trans (add_comm _ _)

/-- The original punctured torus cannot admit a nontrivial full
dilation group about one of its points. The preserved image would be
star-convex and hence contractible. -/
theorem invariant_radial_flow_dilation_zero (s : OriginalSmoothHelicoid) (L : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))
    (a o : Fin 3 → ℝ) (d : ℝ) (radial : ∀ p, a+L p=d • (p-o)) (origin : o ∈ range s.position)
    (pres : ∀ t : ℝ, MapsTo (affineAmbientFlow L a t) (range s.position) (range s.position)) : d=0 := by
  by_contra hd
  have star : StarConvex ℝ o (range s.position) := by
    intro p hp u v hu hv sum
    rcases eq_or_lt_of_le hv with z | pos
    · have uv : u=1 := by linarith
      simpa only [← z,uv,one_smul,zero_smul,add_zero] using origin
    · let t := Real.log v/d
      have dt : d*t=Real.log v := by dsimp [t]; field_simp
      have pt := pres t hp
      rw [affine_radial_flow_position L a o d radial p t,dt,Real.exp_log pos] at pt
      have e : o+v • (p-o)=u • o+v • p := by
        have eu : u=1-v := by linarith
        rw [eu,smul_sub,sub_smul,one_smul]
        abel
      exact e ▸ pt
  let _ := star.contractibleSpace ⟨o,origin⟩
  exact s.not_simply_connected s.closedEmbedding.isEmbedding.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.invariant_axial_rigid_motion_translation_zero
#print axioms TwoAxisHelicoid.invariant_radial_flow_dilation_zero
