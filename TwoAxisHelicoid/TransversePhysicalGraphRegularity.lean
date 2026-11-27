import TwoAxisHelicoid.CoreSheetPlaneConvergence
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology ContDiff RealInnerProductSpace

/-- A continuous solution of a smooth local implicit equation agrees
with the actual implicit inverse near the base point. -/
theorem continuous_implicit_section_contDiffAt {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] {n : ℕ∞ω} (nz : n≠0)
    {H : E × F → G} {g : E → F} {x : E} (cg : ContinuousAt g x)
    (sm : ContDiffAt ℝ n H (x,g x)) (inv : ((fderiv ℝ H (x,g x)).comp (ContinuousLinearMap.inr ℝ E F)).IsInvertible)
    (same : (fun z => H (z,g z)) =ᶠ[𝓝 x] fun _ => H (x,g x)) : ContDiffAt ℝ n g x := by
  have c : ContinuousAt (fun z => (z,g z)) x := continuousAt_id.prodMk cg
  apply (sm.contDiffAt_implicitFunction nz inv).congr_of_eventuallyEq
  filter_upwards [c.tendsto.eventually (sm.eventually_apply_eq_iff_implicitFunction nz inv),same] with z e eq
  exact ((e).mp eq).symm

/-- The two transverse spatial parametrizations determine the moving
parameter and the normal height smoothly in any reference chart. Only
continuity of these two unknown maps is assumed. -/
theorem continuous_transverse_normal_graph_regular {X N Y : ℂ → SurfaceEuclideanSpace}
    {u : ℂ → ℝ} {g : ℂ → ℂ} {z : ℂ} {n : ℕ∞ω} (nz : n≠0)
    (sx : ContDiffAt ℝ n X z) (sn : ContDiffAt ℝ n N z) (sy : ContDiffAt ℝ n Y (g z))
    (inj : Function.Injective (fderiv ℝ Y (g z))) {m : SurfaceEuclideanSpace}
    (perp : ∀ v, ⟪fderiv ℝ Y (g z) v,m⟫=0) (angle : ⟪N z,m⟫≠0)
    (cu : ContinuousAt u z) (cg : ContinuousAt g z)
    (graph : (Y ∘ g) =ᶠ[𝓝 z] (fun w => X w+u w • N w)) :
    ContDiffAt ℝ n g z ∧ ContDiffAt ℝ n u z ∧ ContDiffAt ℝ n (Y ∘ g) z ∧
      ∀ v, ⟪fderiv ℝ (Y ∘ g) z v,m⟫=0 := by
  let s := fun w => (g w,u w)
  let p := (z,s z)
  let H := fun v : ℂ × (ℂ × ℝ) => Y v.2.1-v.2.2 • N v.1-X v.1
  let D := (fderiv ℝ Y (g z)).comp (ContinuousLinearMap.fst ℝ ℂ ℝ)-
    (ContinuousLinearMap.snd ℝ ℂ ℝ).smulRight (N z)
  have sm : ContDiffAt ℝ n H p :=
    ((sy.comp p (contDiffAt_fst.comp p contDiffAt_snd)).sub
      ((contDiffAt_snd.comp p contDiffAt_snd).smul (sn.comp p contDiffAt_fst))).sub (sx.comp p contDiffAt_fst)
  have fiberDerivative : HasFDerivAt (fun v : ℂ × ℝ => H (z,v)) D (s z) :=
    (((sy.differentiableAt nz).hasFDerivAt.comp (s z) (ContinuousLinearMap.fst ℝ ℂ ℝ).hasFDerivAt).sub
      ((ContinuousLinearMap.snd ℝ ℂ ℝ).smulRight (N z)).hasFDerivAt).sub_const (X z)
  have derived := (sm.differentiableAt nz).hasFDerivAt.comp (s z) (hasFDerivAt_prodMk_right z (s z))
  have same : (fderiv ℝ H p).comp (ContinuousLinearMap.inr ℝ ℂ (ℂ × ℝ))=D := derived.unique fiberDerivative
  have di : Function.Injective D := by
    apply (injective_iff_map_eq_zero _).mpr
    rintro ⟨v,t⟩ zero
    change fderiv ℝ Y (g z) v-t • N z=0 at zero
    have test := congrArg (fun w => ⟪w,m⟫) zero
    simp only [inner_sub_left,real_inner_smul_left,perp,inner_zero_left,zero_sub,neg_eq_zero] at test
    have ht := (mul_eq_zero.mp test).resolve_right angle
    subst t
    rw [zero_smul,sub_zero] at zero
    exact Prod.ext (inj (zero.trans (map_zero _).symm)) rfl
  have dims : Module.finrank ℝ (ℂ × ℝ)=Module.finrank ℝ SurfaceEuclideanSpace := by
    simp only [Module.finrank_prod,Complex.finrank_real_complex,Module.finrank_self,finrank_euclideanSpace_fin]
  have bij : Function.Bijective D := ⟨di,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank dims (f := D.toLinearMap)).mp di⟩
  have inv : ((fderiv ℝ H p).comp (ContinuousLinearMap.inr ℝ ℂ (ℂ × ℝ))).IsInvertible := by
    rw [same]
    exact ⟨(LinearEquiv.ofBijective D.toLinearMap bij).toContinuousLinearEquiv,rfl⟩
  have good : ∀ᶠ w in 𝓝 z, H (w,s w)=0 := by
    filter_upwards [graph] with w eq
    change Y (g w)-u w • N w-X w=0
    change Y (g w)=X w+u w • N w at eq
    rw [eq]
    abel
  have rs := continuous_implicit_section_contDiffAt (g := s) nz (cg.prodMk cu) sm inv
    (good.mono (fun w h => h.trans good.self_of_nhds.symm))
  have sg : ContDiffAt ℝ n g z := contDiffAt_fst.comp z rs
  refine ⟨sg,contDiffAt_snd.comp z rs,sy.comp z sg,?_⟩
  intro v
  rw [fderiv_comp z (sy.differentiableAt nz) (sg.differentiableAt nz)]
  exact perp _

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.continuous_implicit_section_contDiffAt
#print axioms TwoAxisHelicoid.continuous_transverse_normal_graph_regular
