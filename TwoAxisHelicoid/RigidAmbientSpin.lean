import TwoAxisHelicoid.OrthogonalQuaternionFrame
import TwoAxisHelicoid.CapOrthonormalSpin
import TwoAxisHelicoid.GeometricExteriorPullback

namespace TwoAxisHelicoid
open Complex Matrix Set Topology
open scoped Topology Matrix ContDiff Manifold

private theorem spatial_gram_orthogonal (T : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ))
    (ho : ∀ x y, T x ⬝ᵥ T y=x ⬝ᵥ y) (a b : Fin 3 → ℝ) :
    spatialGramFrame (T a) (T b)=(T (spatialGramFrame a b).1,T (spatialGramFrame a b).2) := by
  have unit (v) : spatialUnitVector (T v)=T (spatialUnitVector v) := by
    simp only [spatialUnitVector,ho,map_smul]
  dsimp only [spatialGramFrame]
  rw [ho,ho]
  have e : T (b-(a ⬝ᵥ b / a ⬝ᵥ a) • a)=T b-(a ⬝ᵥ b / a ⬝ᵥ a) • T a := by simp
  exact Prod.ext (unit a) ((congrArg spatialUnitVector e.symm).trans (unit _))

private theorem ambient_spin_forward {L : PeriodPair} {F : PeriodTorus L → Fin 3 → ℝ} {i : Fin 2}
    (T : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)) (ho : ∀ x y, T x ⬝ᵥ T y=x ⬝ᵥ y) (b : Fin 3 → ℝ)
    (lift : CapGeneratorAmbientSpinCloses L F i) :
    CapGeneratorAmbientSpinCloses L (fun q => b+T (F q)) i := by
  let S := T.toContinuousLinearEquiv
  obtain ⟨H,hH⟩ := orthogonal_tangent_pair_quaternion_lift T ho
  obtain ⟨u,period,frame⟩ := lift
  refine ⟨H.comp u,congrArg H period,fun r => ?_⟩
  let l := periodBasisLine L i r
  let D := fderiv ℝ (F ∘ periodTorusProjection L) l
  have derivative : fderiv ℝ ((fun q => b+T (F q)) ∘ periodTorusProjection L) l=S.toContinuousLinearMap.comp D := by
    change fderiv ℝ (fun z => b+S ((F ∘ periodTorusProjection L) z)) l=_
    rw [fderiv_const_add]
    exact S.comp_fderiv
  dsimp only
  rw [derivative]
  change (unitQuaternionFrame (H (u r))).1=spatialGramFrame (T (D (L.basis i))) (T (D (I*L.basis i)))
  rw [hH,spatial_gram_orthogonal T ho,frame r]

/-- Both handednesses of rigid ambient coordinates preserve the
generator-by-generator lifting criterion and hence the whole marked
quadratic function of an immersed cap. -/
theorem cap_ambient_spin_quadratic_rigid (L : PeriodPair) (F : PeriodTorus L → Fin 3 → ℝ)
    (R : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ))
    (hR : ∀ v w : Fin 3 → ℝ, (∑ j, (R v j-R w j)^2)=∑ j, (v j-w j)^2) :
    capAmbientSpinQuadratic L (R ∘ F)=capAmbientSpinQuadratic L F := by
  classical
  have forward (J : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ))
      (hJ : ∀ v w : Fin 3 → ℝ, (∑ j, (J v j-J w j)^2)=∑ j, (v j-w j)^2)
      (G : PeriodTorus L → Fin 3 → ℝ) (i : Fin 2) (h : CapGeneratorAmbientSpinCloses L G i) :
      CapGeneratorAmbientSpinCloses L (J ∘ G) i := by
    obtain ⟨T,b,ho,map⟩ := orthogonal_affine_coordinates_of_displacement J hJ
    have eq : J ∘ G=(fun q => b+T (G q)) := funext (fun q => map (G q))
    rw [eq]
    exact ambient_spin_forward T ho b h
  have inverse (x y : Fin 3 → ℝ) : (∑ j,(R.symm x j-R.symm y j)^2)=∑ j,(x j-y j)^2 := by
    simpa only [R.apply_symm_apply] using (hR (R.symm x) (R.symm y)).symm
  have eq (i : Fin 2) : CapGeneratorAmbientSpinCloses L (R ∘ F) i ↔ CapGeneratorAmbientSpinCloses L F i := by
    refine ⟨fun h => ?_,forward R hR F i⟩
    have hh := forward R.symm inverse (R ∘ F) i h
    simpa only [Function.comp_def,R.symm_apply_apply] using hh
  simp only [capAmbientSpinQuadratic,eq]

/-- Pulling a closed cap back through a rigid spatial placement keeps
its smooth structure, its injective differential and its quadratic
function, with no hypothesis on the regular homotopy class of the cap. -/
theorem rigid_coordinates_cap_spin_transfer (L : PeriodPair) (F : PeriodTorus L → Fin 3 → ℝ)
    (cs : ChartedSpace (ℝ × ℝ) (PeriodTorus L)) (R : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ))
    (hR : ∀ v w : Fin 3 → ℝ, (∑ j, (R v j-R w j)^2)=∑ j, (v j-w j)^2) :
    let _ := cs
    IsManifold 𝓘(ℝ,ℝ × ℝ) ∞ (PeriodTorus L) → IsClosedEmbedding F →
    ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F →
    (∀ p, Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) F p)) →
    IsClosedEmbedding (R.symm ∘ F) ∧ ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) ∞ (R.symm ∘ F) ∧
    (∀ p, Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) (R.symm ∘ F) p)) ∧
    capAmbientSpinQuadratic L (R.symm ∘ F)=capAmbientSpinQuadratic L F := by
  intro inst hm closed smooth inj
  have inverse (x y : Fin 3 → ℝ) : (∑ j,(R.symm x j-R.symm y j)^2)=∑ j,(x j-y j)^2 := by
    simpa only [R.apply_symm_apply] using (hR (R.symm x) (R.symm y)).symm
  obtain ⟨T,b,_,hT⟩ := orthogonal_affine_coordinates_of_displacement R.symm inverse
  let S := T.toContinuousLinearEquiv
  let J := fun v : Fin 3 → ℝ => b+S v
  have jj : R.symm=J := funext hT
  let I := 𝓘(ℝ,Fin 3 → ℝ)
  have j : ContMDiff I I ∞ J := (contDiff_const.add S.contDiff).contMDiff
  have jd (v : Fin 3 → ℝ) : mfderiv I I J v=S.toContinuousLinearMap := by
    rw [mfderiv_eq_fderiv]
    exact (S.hasFDerivAt.const_add b).fderiv
  refine ⟨R.symm.isClosedEmbedding.comp closed,jj ▸ j.comp smooth,?_,cap_ambient_spin_quadratic_rigid L F R.symm inverse⟩
  intro x
  rw [jj,mfderiv_comp x (j.mdifferentiable (by simp) _) (smooth.mdifferentiable (by simp) x),jd]
  exact S.injective.comp (inj x)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.cap_ambient_spin_quadratic_rigid
#print axioms TwoAxisHelicoid.rigid_coordinates_cap_spin_transfer
