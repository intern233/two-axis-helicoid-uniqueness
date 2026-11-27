import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace TwoAxisHelicoid
open NormedSpace
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Homogeneous coordinates realize the affine ODE x' = Lx+a as an
autonomous linear ODE on E×ℝ. -/
noncomputable def affineFlowGenerator (L : E →L[ℝ] E) (a : E) : (E × ℝ) →L[ℝ] (E × ℝ) :=
  ((L.comp (ContinuousLinearMap.fst ℝ E ℝ)) + (ContinuousLinearMap.snd ℝ E ℝ).smulRight a).prod 0

noncomputable def homogeneousFlow (L : E →L[ℝ] E) (a : E) (t : ℝ) : (E × ℝ) →L[ℝ] (E × ℝ) :=
  NormedSpace.exp (t • affineFlowGenerator L a)

theorem homogeneousFlow_deriv (L : E →L[ℝ] E) (a : E) (v : E × ℝ) (t : ℝ) :
    HasDerivAt (fun s => homogeneousFlow L a s v)
      (affineFlowGenerator L a (homogeneousFlow L a t v)) t := by
  simpa only [homogeneousFlow,map_zero,add_zero,mul_apply_eq_comp] using
    (hasDerivAt_exp_smul_const' (affineFlowGenerator L a) t).clm_apply (hasDerivAt_const t v)

omit [CompleteSpace E] in
@[simp] theorem homogeneousFlow_zero (L : E →L[ℝ] E) (a : E) (v : E × ℝ) :
    homogeneousFlow L a 0 v = v := by simp [homogeneousFlow]

theorem homogeneousFlow_add (L : E →L[ℝ] E) (a : E) (v : E × ℝ) (s t : ℝ) :
    homogeneousFlow L a (s+t) v = homogeneousFlow L a s (homogeneousFlow L a t v) := by
  let G := affineFlowGenerator L a
  have hball (r : ℝ) : r • G ∈ Metric.eball 0 (expSeries ℝ ((E×ℝ) →L[ℝ] (E×ℝ))).radius := by
    rw [expSeries_radius_eq_top]
    exact edist_lt_top _ _
  change exp ((s+t) • G) v = exp (s • G) (exp (t • G) v)
  rw [add_smul,exp_add_of_commute_of_mem_ball (((Commute.refl G).smul_left s).smul_right t) (hball s) (hball t)]
  rfl

theorem homogeneousFlow_snd (L : E →L[ℝ] E) (a : E) (v : E × ℝ) (t : ℝ) :
    (homogeneousFlow L a t v).2 = v.2 := by
  have h (s : ℝ) : HasDerivAt (fun r => (homogeneousFlow L a r v).2) 0 s :=
    (homogeneousFlow_deriv L a v s).snd
  simpa using is_const_of_deriv_eq_zero (fun s => (h s).differentiableAt) (fun s => (h s).deriv) t 0

noncomputable def affineAmbientFlow (L : E →L[ℝ] E) (a : E) (t : ℝ) (x : E) : E :=
  (homogeneousFlow L a t (x,1)).1

noncomputable def affineAmbientLinearPart (L : E →L[ℝ] E) (a : E) (t : ℝ) : E →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ E ℝ).comp ((homogeneousFlow L a t).comp (ContinuousLinearMap.inl ℝ E ℝ))

omit [CompleteSpace E] in
@[simp] theorem affineAmbientFlow_zero (L : E →L[ℝ] E) (a x : E) :
    affineAmbientFlow L a 0 x = x := by simp [affineAmbientFlow]

theorem affineAmbientFlow_deriv (L : E →L[ℝ] E) (a x : E) (t : ℝ) :
    HasDerivAt (fun s => affineAmbientFlow L a s x) (a+L (affineAmbientFlow L a t x)) t := by
  have h := (homogeneousFlow_deriv L a (x,1) t).fst
  change HasDerivAt (fun s : ℝ => affineAmbientFlow L a s x) (L (affineAmbientFlow L a t x)+(homogeneousFlow L a t (x,1)).2 • a) t at h
  simpa only [homogeneousFlow_snd,one_smul,add_comm] using h

theorem affineAmbientLinearPart_deriv (L : E →L[ℝ] E) (a x : E) (t : ℝ) :
    HasDerivAt (fun s => affineAmbientLinearPart L a s x) (L (affineAmbientLinearPart L a t x)) t := by
  have h := (homogeneousFlow_deriv L a (x,0) t).fst
  change HasDerivAt (fun s : ℝ => affineAmbientLinearPart L a s x) (L (affineAmbientLinearPart L a t x)+(homogeneousFlow L a t (x,0)).2 • a) t at h
  simpa only [homogeneousFlow_snd,zero_smul,add_zero] using h

theorem affineAmbientFlow_add (L : E →L[ℝ] E) (a x : E) (s t : ℝ) :
    affineAmbientFlow L a (s+t) x = affineAmbientFlow L a s (affineAmbientFlow L a t x) := by
  have he : homogeneousFlow L a t (x,1) = (affineAmbientFlow L a t x,1) :=
    Prod.ext rfl (homogeneousFlow_snd L a (x,1) t)
  unfold affineAmbientFlow
  rw [homogeneousFlow_add,he]

omit [CompleteSpace E] in
theorem affineAmbientFlow_linear_part (L : E →L[ℝ] E) (a x : E) (t : ℝ) :
    affineAmbientFlow L a t x = affineAmbientLinearPart L a t x + affineAmbientFlow L a t 0 := by
  have he : (x,(1:ℝ)) = (x,0)+(0,1) := by simp
  unfold affineAmbientFlow
  rw [he,map_add]
  rfl

omit [CompleteSpace E] in
theorem affineAmbientFlow_hasFDerivAt (L : E →L[ℝ] E) (a x : E) (t : ℝ) :
    HasFDerivAt (affineAmbientFlow L a t) (affineAmbientLinearPart L a t) x := by
  convert (affineAmbientLinearPart L a t).hasFDerivAt.add_const (affineAmbientFlow L a t 0) using 1
  funext p
  exact affineAmbientFlow_linear_part L a p t

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.affineAmbientFlow_deriv
#print axioms TwoAxisHelicoid.affineAmbientFlow_add
