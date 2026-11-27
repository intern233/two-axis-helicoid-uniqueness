import TwoAxisHelicoid.EssentialTorusPlaneSection
import TwoAxisHelicoid.RegularHomotopyGeneratorParity
import TwoAxisHelicoid.HorizontalGraphHeightChart

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace
open scoped ContDiff Manifold RealInnerProductSpace unitInterval

private noncomputable def slopeFunctional (s : ℂ) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ s).comp (spatialGraphProjection 0 1)

/-- The shear taking a plane of slope s to a horizontal plane leaves both
horizontal coordinates fixed. Its values at all intermediate times are linear. -/
noncomputable def heightPlaneShear (s : ℂ) (t : ℝ) : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.id ℝ _ - t • (slopeFunctional s).smulRight ![0,0,1]

private theorem shear_apply (s : ℂ) (t : ℝ) (v : Fin 3 → ℝ) :
    heightPlaneShear s t v=v-(t*slopeFunctional s v) • ![0,0,1] := by
  simp [heightPlaneShear]

theorem heightPlaneShear_vertical (s : ℂ) (t : ℝ) (v : Fin 3 → ℝ) :
    heightPlaneShear s t v 2=v 2-t*⟪s,spatialGraphProjection 0 1 v⟫_ℝ := by
  rw [shear_apply]
  simp [slopeFunctional]

theorem heightPlaneShear_injective (s : ℂ) (t : ℝ) : Function.Injective (heightPlaneShear s t) := by
  have vert : slopeFunctional s ![0,0,1]=0 := by
    change ⟪s,(⟨0,0⟩:ℂ)⟫_ℝ=0
    exact inner_zero_right _
  intro x y eq
  rw [shear_apply,shear_apply] at eq
  have slope := congrArg (slopeFunctional s) eq
  simp only [map_sub,map_smul,vert,smul_zero,sub_zero] at slope
  rw [slope] at eq
  exact sub_left_inj.mp eq

/-- Flattening a tilted plane preserves evenness of the induced torus spin.
The homotopy is through explicit linear shears and only needs the original
punctured marking to be regular along the two marked generators. -/
theorem cap_arf_even_of_height_shear (L : PeriodPair) (F : PeriodTorus L → Fin 3 → ℝ)
    (sm : ∀ q≠0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F q)
    (imm : ∀ q≠0, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) F q))
    (s : ℂ) (parity : capAmbientSpinQuadratic L (heightPlaneShear s 1 ∘ F) (1,0) *
      capAmbientSpinQuadratic L (heightPlaneShear s 1 ∘ F) (0,1)=0) :
    capAmbientSpinQuadratic L F (1,0)*capAmbientSpinQuadratic L F (0,1)=0 := by
  let π := periodTorusProjection L
  let H := fun t : unitInterval => heightPlaneShear s t.1 ∘ F
  have reg (i : Fin 2) (t : ℝ) := spatial_torus_lift_regular_at L F
    (periodBasisLine_not_mem_lattice L i t) sm imm
  have eq (i : Fin 2) (w : unitInterval × unitInterval) :
      fderiv ℝ (H w.1 ∘ π) (periodBasisLine L i w.2.1)=
      (heightPlaneShear s w.1.1).comp (fderiv ℝ (F ∘ π) (periodBasisLine L i w.2.1)) :=
    ((heightPlaneShear s w.1.1).hasFDerivAt.comp _ ((reg i w.2.1).1.differentiableAt (by simp)).hasFDerivAt).fderiv
  have zero : H 0=F := by funext p; simp [H,heightPlaneShear]
  rw [← zero]
  apply marked_arf_even_of_regular_homotopy L H _ _ parity
  · intro i
    change Continuous (fun w : unitInterval × unitInterval => fderiv ℝ (H w.1 ∘ π) (periodBasisLine L i w.2.1))
    simp_rw [eq]
    apply Continuous.clm_comp
    · exact continuous_const.sub ((continuous_subtype_val.comp continuous_fst).smul continuous_const)
    · have path : Continuous (fun w : unitInterval × unitInterval => periodBasisLine L i w.2.1) := by
        unfold periodBasisLine; fun_prop
      apply continuous_iff_continuousAt.mpr
      intro w
      have d : ContinuousAt (fderiv ℝ (F ∘ π)) (periodBasisLine L i w.2.1) :=
        (reg i w.2.1).1.continuousAt_fderiv (by simp)
      exact d.tendsto.comp (path.continuousAt (x:=w)).tendsto
  · intro i w
    change Function.Injective (fderiv ℝ (H w.1 ∘ π) (periodBasisLine L i w.2.1))
    rw [eq]
    exact (heightPlaneShear_injective s _).comp (reg i w.2.1).2

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.cap_arf_even_of_height_shear
