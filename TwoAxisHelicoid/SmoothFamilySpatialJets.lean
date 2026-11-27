module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.NormNum

public section

namespace TwoAxisHelicoid
open Filter Topology
open scoped ContDiff Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private noncomputable def column (a : ℝ × ℂ) (F : ℝ × ℂ → V) (q : ℝ × ℂ) :=
  fderiv ℝ F q a

private noncomputable def spaceColumn (v : ℂ) (F : ℝ × ℂ → V) (q : ℝ × ℂ) :=
  fderiv ℝ (fun w => F (q.1,w)) q.2 v

private noncomputable def timeColumn (F : ℝ × ℂ → V) (q : ℝ × ℂ) :=
  deriv (fun s => F (s,q.2)) q.1

private theorem space_column_eq {F : ℝ × ℂ → V} {q : ℝ × ℂ}
    (h : DifferentiableAt ℝ F q) (v : ℂ) : spaceColumn v F q = column (0,v) F q :=
  congrArg (fun L : ℂ →L[ℝ] V => L v)
    (h.hasFDerivAt.comp q.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2)).fderiv

private theorem time_column_hasDerivAt {F : ℝ × ℂ → V} {q : ℝ × ℂ}
    (h : DifferentiableAt ℝ F q) : HasDerivAt (fun s => F (s,q.2)) (column (1,0) F q) q.1 :=
  h.hasFDerivAt.comp_hasDerivAt q.1 ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2))

private theorem space_column_congr {F G : ℝ × ℂ → V} {q : ℝ × ℂ}
    (eq : F =ᶠ[𝓝 q] G) (v : ℂ) : spaceColumn v F q = spaceColumn v G q :=
  congrArg (fun L : ℂ →L[ℝ] V => L v)
    (eq.comp_tendsto ((continuous_const.prodMk continuous_id).tendsto q.2)).fderiv_eq

private theorem column_eq_hessian {P W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F : P → W} {p : P}
    (h : ContDiffAt ℝ 2 F p) (a b : P) :
    fderiv ℝ (fun x => fderiv ℝ F x b) p a = fderiv ℝ (fderiv ℝ F) p a b := by
  have df := ((h.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  exact congrArg (fun L : P →L[ℝ] W => L a)
    ((ContinuousLinearMap.apply ℝ W b).hasFDerivAt.comp p df).fderiv

private theorem mixed_time_first_column {F : ℝ × ℂ → V} {q : ℝ × ℂ}
    (h : ContDiffAt ℝ 2 F q) (v : ℂ) :
    HasDerivAt (fun s => spaceColumn v F (s,q.2)) (spaceColumn v (timeColumn F) q) q.1 := by
  have near := (h.eventually (by norm_num)).mono (fun _ hp => hp.differentiableAt two_ne_zero)
  have se : spaceColumn v F =ᶠ[𝓝 q] column (0,v) F := near.mono fun _ hp => space_column_eq hp v
  have te : timeColumn F =ᶠ[𝓝 q] column (1,0) F := near.mono fun _ hp => (time_column_hasDerivAt hp).deriv
  have dc (a : ℝ × ℂ) : DifferentiableAt ℝ (column a F) q :=
    ((h.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt one_ne_zero
  have swap : column (1,0) (column (0,v) F) q = column (0,v) (column (1,0) F) q := by
    unfold column
    rw [column_eq_hessian h, column_eq_hessian h]
    exact h.isSymmSndFDerivAt (by simp) _ _
  rw [space_column_congr te v,space_column_eq (dc (1,0)) v,← swap]
  exact (time_column_hasDerivAt (dc (0,v))).congr_of_eventuallyEq
    (se.comp_tendsto ((continuous_id.prodMk continuous_const).tendsto q.1))

/-- For a jointly C³ variation the time derivatives of the spatial first and second
derivatives are the matching derivatives of the genuine pointwise velocity. -/
theorem joint_c3_spatial_jet_velocity {F : ℝ → ℂ → V} {s : ℝ} {z : ℂ}
    (smooth : ContDiffAt ℝ 3 (fun q : ℝ × ℂ => F q.1 q.2) (s,z)) :
    let W := fun w => deriv (fun r => F r w) s
    ContDiffAt ℝ 2 W z ∧
      (∀ v, HasDerivAt (fun r => fderiv ℝ (F r) z v) (fderiv ℝ W z v) s) ∧
      ∀ v w, HasDerivAt (fun r => fderiv ℝ (fderiv ℝ (F r)) z v w)
        (fderiv ℝ (fderiv ℝ W) z v w) s := by
  intro W
  let G := fun q : ℝ × ℂ => F q.1 q.2
  have near : ∀ᶠ q in 𝓝 (s,z), ContDiffAt ℝ 3 G q := smooth.eventually (by norm_num)
  have t2 : ContDiffAt ℝ 2 (timeColumn G) (s,z) := by
    apply ((smooth.fderiv_right (m := 2) (by norm_num)).clm_apply
      (contDiffAt_const (c := ((1:ℝ),(0:ℂ))))).congr_of_eventuallyEq
    exact near.mono fun _ hp => (time_column_hasDerivAt (hp.differentiableAt (by norm_num))).deriv
  have cw : ContDiffAt ℝ 2 W z := t2.comp z (contDiffAt_const.prodMk contDiffAt_id)
  refine ⟨cw,mixed_time_first_column (smooth.of_le (show (2:ℕ∞ω) ≤ 3 by norm_num)),?_⟩
  intro v w
  have s2 : ContDiffAt ℝ 2 (spaceColumn w G) (s,z) := by
    apply ((smooth.fderiv_right (m := 2) (by norm_num)).clm_apply
      (contDiffAt_const (c := ((0:ℝ),w)))).congr_of_eventuallyEq
    exact near.mono fun _ hp => space_column_eq (hp.differentiableAt (by norm_num)) w
  have change_order : timeColumn (spaceColumn w G) =ᶠ[𝓝 (s,z)] spaceColumn w (timeColumn G) :=
    near.mono fun _ hp => (mixed_time_first_column (hp.of_le (show (2:ℕ∞ω) ≤ 3 by norm_num)) w).deriv
  have atS : spaceColumn v (timeColumn (spaceColumn w G)) (s,z) = fderiv ℝ (fderiv ℝ W) z v w :=
    (space_column_congr change_order v).trans (column_eq_hessian cw v w)
  rw [← atS]
  apply (mixed_time_first_column s2 v).congr_of_eventuallyEq
  filter_upwards [((continuous_id.prodMk continuous_const).tendsto s).eventually near] with r hr
  have cr : ContDiffAt ℝ 2 (F r) z :=
    (hr.of_le (show (2:ℕ∞ω) ≤ 3 by norm_num)).comp z (contDiffAt_const.prodMk contDiffAt_id)
  exact (column_eq_hessian cr v w).symm

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.joint_c3_spatial_jet_velocity
