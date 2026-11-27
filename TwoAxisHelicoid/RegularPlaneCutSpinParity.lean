import TwoAxisHelicoid.PuncturedCompressingDiskParity
import TwoAxisHelicoid.IntegerBranchPlanarObstruction

namespace TwoAxisHelicoid
open Complex Set Matrix
open scoped Topology ContDiff Manifold Matrix

private noncomputable def spatial_horizontal_projection : (Fin 3 → ℝ) →L[ℝ] ℂ :=
  Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.proj (0 : Fin 3)).prod (ContinuousLinearMap.proj (1 : Fin 3)))

/-- The transverse column of a regular height section has nonzero
vertical component, including for a nonconformal parametrization. -/
private theorem transverse_gram_height {D : ℂ →L[ℝ] (Fin 3 → ℝ)} {v : ℂ}
    (di : Function.Injective D) (nv : v≠0) (zero : D v 2=0)
    (regular : ∃ w, D w 2≠0) :
    (spatialDifferentialFrame di nv).1.1 2=0 ∧ (spatialDifferentialFrame di nv).1.2 2≠0 := by
  let K := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) (2:Fin 3)).ker
  have first : (spatialDifferentialFrame di nv).1.1 2=0 := by
    change (Real.sqrt (D v ⬝ᵥ D v))⁻¹*D v 2=0
    rw [zero,mul_zero]
  refine ⟨first,fun second => ?_⟩
  have both := (spatialGramFrame_mem_iff K (D v) (D (I*v))).mp ⟨first,second⟩
  have zz : D (I*v) 2=0 := both.2
  obtain ⟨w,h⟩ := regular
  let c := w/v
  have eq : c.re • v+c.im • (I*v)=w := by
    rw [Complex.real_smul,Complex.real_smul,← mul_assoc,← add_mul,Complex.re_add_im]
    exact div_mul_cancel₀ _ nv
  apply h
  rw [← eq,map_add,map_smul,map_smul,Pi.add_apply,Pi.smul_apply,Pi.smul_apply,zero,zz,smul_zero,zero_add,smul_zero]

/-- A regular horizontal section with one simple essential component
already forces even spin of an embedded torus. The section only has
to avoid the marked point where a capping chart may differ. No
spanning disk, solid-side parametrization or regular homotopy is used. -/
theorem embedded_torus_regular_plane_section_even (L : PeriodPair) (F : PeriodTorus L → Fin 3 → ℝ)
    (embed : Function.Injective F)
    (sm : ∀ q≠0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F q)
    (imm : ∀ q≠0, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) F q))
    {ξ : ℝ → ℂ} (smooth : ContDiff ℝ 1 ξ) (off : ∀ t, ξ t∉L.lattice) {period : ℂ} (nz : period≠0)
    (lat : period∈L.lattice) (per : ∀ t, ξ (t+1)=ξ t+period) (reg : ∀ t, deriv ξ t≠0)
    (simple : ∀ t h : ℝ, h∈Ioo (0:ℝ) 1 → periodTorusProjection L (ξ (t+h))≠periodTorusProjection L (ξ t))
    {h : ℝ} (height : ∀ t, F (periodTorusProjection L (ξ t)) 2=h)
    (heightReg : ∀ t, ∃ w, fderiv ℝ (F ∘ periodTorusProjection L) (ξ t) w 2≠0) :
    capAmbientSpinQuadratic L F (1,0)*capAmbientSpinQuadratic L F (0,1)=0 := by
  let Y := F ∘ periodTorusProjection L
  let A := fun t => Y (ξ t)
  let D := fun t => fderiv ℝ Y (ξ t)
  let v := deriv ξ
  let P := spatial_horizontal_projection
  let γ := P ∘ A
  have surf (t : ℝ) := spatial_torus_lift_regular_at L F (off t) sm imm
  have da (t : ℝ) : HasDerivAt A (D t (v t)) t :=
    ((surf t).1.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t ((smooth.differentiable (by simp) t).hasDerivAt)
  have dg (t : ℝ) : HasDerivAt γ (P (D t (v t))) t := P.hasFDerivAt.comp_hasDerivAt t (da t)
  have hz (t : ℝ) : D t (v t) 2=0 := by
    have d := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) (2:Fin 3)).hasFDerivAt.comp_hasDerivAt t (da t)
    exact (d.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => (height x).symm)).unique (hasDerivAt_const t h)
  have hγ : ContDiff ℝ 1 γ := contDiff_iff_contDiffAt.mpr fun t =>
    P.contDiff.contDiffAt.comp t (((surf t).1.of_le (by simp)).comp t smooth.contDiffAt)
  have pγ : Function.Periodic γ 1 := fun t => by
    change P (F (periodTorusProjection L (ξ (t+1))))=_
    rw [per,periodTorusProjection_add_lattice L _ _ lat]
    rfl
  have rγ (t : ℝ) : deriv γ t≠0 := by
    rw [(dg t).deriv]
    intro e
    have x := congrArg Complex.re e
    have y := congrArg Complex.im e
    have n : D t (v t)=0 := by
      ext j
      fin_cases j
      · exact x
      · exact y
      · exact hz t
    exact reg t ((surf t).2 (n.trans (D t).map_zero.symm))
  have iγ (t h : ℝ) (ht : h∈Ioo (0:ℝ) 1) : γ (t+h)≠γ t := by
    intro e
    apply simple t h ht
    apply embed
    ext j
    fin_cases j
    · exact congrArg Complex.re e
    · exact congrArg Complex.im e
    · exact (height _).trans (height _).symm
  have obstruct : ¬∀ i, CapGeneratorAmbientSpinCloses L F i := by
    intro gen
    obtain ⟨q,closed,qu⟩ := punctured_ambient_lift_on_essential_curve L sm imm gen smooth off nz lat per reg
      (fun t h hh e => simple t h hh (congrArg (periodTorusProjection L) e))
    have transverse (t : unitInterval) := transverse_gram_height (surf t.1).2 (reg t.1) (hz t.1) (heightReg t.1)
    have eq (t : unitInterval) : frameHorizontalTangent (q t)=unitComplexDirection (deriv γ t.1) (rγ _) := by
      have positive : 0<(Real.sqrt (D t (v t) ⬝ᵥ D t (v t)))⁻¹ :=
        inv_pos.mpr (Real.sqrt_pos.mpr (spatial_dot_self_pos (fun eq => reg t.1 ((surf t.1).2 (eq.trans (D t).map_zero.symm)))))
      apply frameHorizontalTangent_direction (q t) (by rw [qu]; exact (transverse t).1) (rγ _) positive
      rw [(dg t.1).deriv]
      apply Complex.ext <;> simp [frameHorizontalTangent,qu,spatialDifferentialFrame,spatialGramFrame,spatialUnitVector,P,spatial_horizontal_projection,Complex.mul_re,Complex.mul_im,D,v,Y]
    exact transverse_planar_section_quaternion_lift_not_closed hγ pγ rγ iγ q
      (fun t => by rw [qu]; exact (transverse t).1) (fun t => by rw [qu]; exact (transverse t).2) eq closed
  by_cases h₀ : CapGeneratorAmbientSpinCloses L F 0
  · have h₁ : ¬CapGeneratorAmbientSpinCloses L F 1 := fun b => obstruct (by intro i; fin_cases i <;> assumption)
    simp [capAmbientSpinQuadratic,torusQuadratic,h₀,h₁]
  · simp [capAmbientSpinQuadratic,torusQuadratic,h₀]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.embedded_torus_regular_plane_section_even
