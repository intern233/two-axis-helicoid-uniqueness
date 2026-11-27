import TwoAxisHelicoid.SmoothImmersionLeftInverse
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith

namespace TwoAxisHelicoid
open Set Filter Matrix Complex Topology
open scoped Topology ContDiff

private theorem time_graph_immersion {F : ℝ × ℂ → Fin 3 → ℝ} {z : ℂ}
    (smooth : ContDiffAt ℝ ∞ F (0,z))
    (imm : Function.Injective (fderiv ℝ (fun w => F (0,w)) z)) :
    Function.Injective (fderiv ℝ (fun a : ℝ × ℂ => (a.1,F a)) (0,z)) := by
  let D := fderiv ℝ F (0,z)
  have dF : HasFDerivAt F D (0,z) := (smooth.differentiableAt (by simp)).hasFDerivAt
  have slice := (dF.comp z (hasFDerivAt_prodMk_right (𝕜 := ℝ) (0:ℝ) z)).fderiv
  have full := (hasFDerivAt_fst (𝕜 := ℝ) (p := ((0:ℝ),z))).prodMk dF
  rw [full.fderiv]
  rintro ⟨s,a⟩ ⟨t,b⟩ h
  change (s,D (s,a)) = (t,D (t,b)) at h
  have sameTime := congrArg Prod.fst h
  change s = t at sameTime
  subst t
  have same : D (s,a) = D (s,b) := congrArg Prod.snd h
  have split (w : ℂ) : D (s,w) = D (s,0) + D (0,w) := by
    rw [← map_add]
    exact congrArg D (Prod.ext (add_zero s).symm (zero_add w).symm)
  rw [split a,split b] at same
  apply congrArg (Prod.mk s)
  apply imm
  change fderiv ℝ (F ∘ fun w : ℂ => ((0:ℝ),w)) z a =
    fderiv ℝ (F ∘ fun w : ℂ => ((0:ℝ),w)) z b
  rw [slice]
  exact add_left_cancel same

/-- The parameter of a moving point on a smooth family of immersed charts is
smooth whenever the spatial path is smooth and the parameter stays on its
local sheet. The time coordinate separates the parameter and surface derivatives. -/
theorem moving_surface_parameter_contDiffAt {F : ℝ × ℂ → Fin 3 → ℝ}
    {c : ℝ → ℂ} {y : ℝ → Fin 3 → ℝ} (smooth : ContDiffAt ℝ ∞ F (0,c 0))
    (imm : Function.Injective (fderiv ℝ (fun w => F (0,w)) (c 0)))
    (branch : ContinuousAt c 0) (path : ContDiffAt ℝ ∞ y 0)
    (track : ∀ᶠ s in 𝓝 (0:ℝ), F (s,c s) = y s) : ContDiffAt ℝ ∞ c 0 := by
  let G := fun a : ℝ × ℂ => (a.1,F a)
  let k := fun s : ℝ => (s,c s)
  have comp : ContDiffAt ℝ ∞ (G ∘ k) 0 := by
    apply (contDiff_id.contDiffAt.prodMk path).congr_of_eventuallyEq
    exact track.mono fun s h => Prod.ext rfl h
  have lift : ContDiffAt ℝ ∞ k 0 :=
    contDiffAt_of_comp_immersion (contDiff_fst.contDiffAt.prodMk smooth)
      (time_graph_immersion smooth imm) (continuousAt_id.prodMk branch) comp
  exact contDiff_snd.contDiffAt.comp 0 lift

/-- Local chart version of D.2. Differentiate the moving reflected point and
remove the spatial derivative of its reparametrization by normal projection. -/
theorem moving_reflection_normal_velocity_odd {F : ℝ × ℂ → Fin 3 → ℝ}
    {c : ℝ → ℂ} {x : ℝ → Fin 3 → ℝ} {v w n m : Fin 3 → ℝ}
    (R : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))
    (orth : ∀ a b, R a ⬝ᵥ R b = a ⬝ᵥ b)
    (smooth : ContDiffAt ℝ ∞ F (0,c 0))
    (imm : Function.Injective (fderiv ℝ (fun z => F (0,z)) (c 0)))
    (branch : ContinuousAt c 0) (path : ContDiffAt ℝ ∞ x 0)
    (reflects : ∀ᶠ s in 𝓝 (0:ℝ), F (s,c s) = R (x s))
    (vx : HasDerivAt x v 0) (vw : HasDerivAt (fun s => F (s,c 0)) w 0)
    (normal : ∀ h, fderiv ℝ (fun z => F (0,z)) (c 0) h ⬝ᵥ m = 0)
    (orientation : m = -R n) : w ⬝ᵥ m = -(v ⬝ᵥ n) := by
  let D := fderiv ℝ F (0,c 0)
  have dF : HasFDerivAt F D (0,c 0) := (smooth.differentiableAt (by simp)).hasFDerivAt
  have smoothC := moving_surface_parameter_contDiffAt smooth imm branch
    (R.contDiff.contDiffAt.comp 0 path) reflects
  have derivC := (smoothC.differentiableAt (by simp)).hasDerivAt
  have moving := dF.comp_hasDerivAt 0 ((hasDerivAt_id (0:ℝ)).prodMk derivC)
  have velocity : D (1,deriv c 0) = R v :=
    moving.unique ((R.hasFDerivAt.comp_hasDerivAt 0 vx).congr_of_eventuallyEq reflects)
  have fixed : D (1,0) = w :=
    (dF.comp_hasDerivAt 0 ((hasDerivAt_id (0:ℝ)).prodMk (hasDerivAt_const 0 (c 0)))).unique vw
  have slice := (dF.comp (c 0) (hasFDerivAt_prodMk_right (𝕜 := ℝ) (0:ℝ) (c 0))).fderiv
  have tangent : D (0,deriv c 0) ⬝ᵥ m = 0 := by
    have h := normal (deriv c 0)
    change fderiv ℝ (F ∘ fun z : ℂ => ((0:ℝ),z)) (c 0) (deriv c 0) ⬝ᵥ m = 0 at h
    rw [slice] at h
    exact h
  have split : D (1,deriv c 0) = D (1,0) + D (0,deriv c 0) := by
    rw [← map_add]
    exact congrArg D (Prod.ext (add_zero (1:ℝ)).symm (zero_add (deriv c 0)).symm)
  calc w ⬝ᵥ m = (D (1,0) + D (0,deriv c 0)) ⬝ᵥ m := by rw [add_dotProduct,tangent,add_zero,fixed]
       _ = R v ⬝ᵥ m := by rw [← split,velocity]
       _ = -(v ⬝ᵥ n) := by rw [orientation,dotProduct_neg,orth]

/-- A jointly embedded family lifts reflected positions continuously from
membership of those positions in the nearby slice images. No choice of a
family of involutions or common markings is needed. -/
theorem embedded_family_reflected_parameter {M : Type*} [TopologicalSpace M]
    (X : ℝ → M → Fin 3 → ℝ) (p q : M) (R : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))
    (emb : IsEmbedding (fun a : ℝ × M => (a.1,X a.1 a.2)))
    (atZero : X 0 q = R (X 0 p))
    (inImage : ∀ᶠ s in 𝓝 (0:ℝ), R (X s p) ∈ range (X s)) :
    ∃ r : ℝ → M, r 0 = q ∧ ContinuousAt r 0 ∧
      ∀ᶠ s in 𝓝 (0:ℝ), X s (r s) = R (X s p) := by
  classical
  let r (s : ℝ) : M := if h : R (X s p) ∈ range (X s) then h.choose else p
  have eq : ∀ᶠ s in 𝓝 (0:ℝ), X s (r s) = R (X s p) := by
    filter_upwards [inImage] with s hs
    simpa only [r,dite_eq_left hs] using hs.choose_spec
  have atBase : ((0:ℝ),r 0) = (0,q) := emb.injective
    (Prod.ext rfl (eq.self_of_nhds.trans atZero.symm))
  have cx : Continuous (fun s : ℝ => X s p) :=
    continuous_snd.comp (emb.continuous.comp (continuous_id.prodMk continuous_const))
  have lift : ContinuousAt (fun s : ℝ => (s,r s)) 0 := by
    apply emb.isInducing.continuousAt_iff.mpr
    apply (continuousAt_id.prodMk (R.continuous.comp cx).continuousAt).congr_of_eventuallyEq
    exact eq.mono fun s h => Prod.ext rfl h
  exact ⟨r,congrArg Prod.snd atBase,continuous_snd.continuousAt.comp lift,eq⟩

/-- For an unmarked embedded family, image symmetry implies odd normal
velocity at reflected points. At a fixed point of the reflection that
velocity is zero. All derivatives are taken in a chart at the reflected point. -/
theorem unmarked_reflection_family_normal_velocity {M : Type*} [TopologicalSpace M]
    (X : ℝ → M → Fin 3 → ℝ) (p q : M) (V N : M → Fin 3 → ℝ)
    (R : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) (orth : ∀ a b, R a ⬝ᵥ R b = a ⬝ᵥ b)
    (emb : IsEmbedding (fun a : ℝ × M => (a.1,X a.1 a.2)))
    (atZero : X 0 q = R (X 0 p))
    (inImage : ∀ᶠ s in 𝓝 (0:ℝ), R (X s p) ∈ range (X s))
    (e : OpenPartialHomeomorph M ℂ) (hq : q ∈ e.source)
    (smooth : ContDiffAt ℝ ∞ (fun a : ℝ × ℂ => X a.1 (e.symm a.2)) (0,e q))
    (imm : Function.Injective (fderiv ℝ (fun z => X 0 (e.symm z)) (e q)))
    (path : ContDiffAt ℝ ∞ (fun s => X s p) 0)
    (vp : HasDerivAt (fun s => X s p) (V p) 0) (vq : HasDerivAt (fun s => X s q) (V q) 0)
    (normal : ∀ h, fderiv ℝ (fun z => X 0 (e.symm z)) (e q) h ⬝ᵥ N q = 0)
    (orientation : N q = -R (N p)) :
    V q ⬝ᵥ N q = -(V p ⬝ᵥ N p) ∧ (q = p → V p ⬝ᵥ N p = 0) := by
  obtain ⟨r,base,cr,acts⟩ := embedded_family_reflected_parameter X p q R emb atZero inImage
  let c := e ∘ r
  have baseC : c 0 = e q := congrArg e base
  have hr : r 0 ∈ e.source := by rw [base]; exact hq
  have branch : ContinuousAt c 0 := (e.continuousAt hr).comp cr
  have track : ∀ᶠ s in 𝓝 (0:ℝ), X s (e.symm (c s)) = R (X s p) := by
    filter_upwards [acts,cr.eventually (e.open_source.mem_nhds hr)] with s hs he
    exact (congrArg (X s) (e.left_inv he)).trans hs
  have odd : V q ⬝ᵥ N q = -(V p ⬝ᵥ N p) := moving_reflection_normal_velocity_odd
    (F := fun a : ℝ × ℂ => X a.1 (e.symm a.2)) (c := c) R orth
    (baseC.symm ▸ smooth) (baseC.symm ▸ imm) branch path track vp
    (by simpa only [baseC,e.left_inv hq] using vq) (baseC.symm ▸ normal) orientation
  refine ⟨odd,?_⟩
  rintro rfl
  linarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.moving_surface_parameter_contDiffAt
#print axioms TwoAxisHelicoid.moving_reflection_normal_velocity_odd
#print axioms TwoAxisHelicoid.embedded_family_reflected_parameter
#print axioms TwoAxisHelicoid.unmarked_reflection_family_normal_velocity
