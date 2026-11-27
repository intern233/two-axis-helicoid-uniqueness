import TwoAxisHelicoid.RegularMinimalIsothermal

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff
set_option maxHeartbeats 1600000

noncomputable def planeMetricArea (E F G : ℂ → ℝ) (z : ℂ) : ℝ := Real.sqrt (E z*G z-(F z)^2)

/-- Divergence of the metric gradient of the first real coordinate, after
multiplication by the positive area density. -/
def FirstCoordinateMetricHarmonicAt (E F G : ℂ → ℝ) (z : ℂ) : Prop :=
  fderiv ℝ (fun w => G w/planeMetricArea E F G w) z 1 =
    fderiv ℝ (fun w => F w/planeMetricArea E F G w) z I

/-- A smooth closed real one-form on a convex plane domain admits a
smooth primitive. Both partial derivatives are the given coefficients. -/
theorem smooth_plane_primitive {U : Set ℂ} (op : IsOpen U) (conv : Convex ℝ U)
    {a b : ℂ → ℝ} (sa : ∀ z∈U, ContDiffAt ℝ ∞ a z) (sb : ∀ z∈U, ContDiffAt ℝ ∞ b z)
    (closed : ∀ z∈U, fderiv ℝ b z 1 = fderiv ℝ a z I) :
    ∃ h : ℂ → ℝ, ∀ z∈U, ContDiffAt ℝ ∞ h z ∧
      HasFDerivAt h (a z • reCLM + b z • imCLM) z := by
  let form := fun z => a z • reCLM + b z • imCLM
  have sf (z : ℂ) (hz : z∈U) : ContDiffAt ℝ ∞ form z :=
    ((sa z hz).smul contDiffAt_const).add ((sb z hz).smul contDiffAt_const)
  have symm (z : ℂ) (hz : z∈U) (v w : ℂ) :
      fderiv ℝ form z v w=fderiv ℝ form z w v := by
    apply complex_bilinear_symm_of_basis
    have line (v w : ℂ) : HasDerivAt (fun s : ℝ => form (z+s • v) w) (fderiv ℝ form z v w) 0 := by
      simpa only [map_zero,add_zero] using!
        (graph_line_deriv ((sf z hz).differentiableAt (by simp)) v).clm_apply (hasDerivAt_const (0:ℝ) w)
    have B := graph_line_deriv ((sb z hz).differentiableAt (by simp)) 1
    have A := graph_line_deriv ((sa z hz).differentiableAt (by simp)) I
    have hB := (line 1 I).unique (B.congr_of_eventuallyEq (Eventually.of_forall fun s => by simp [form]))
    have hA := (line I 1).unique (A.congr_of_eventuallyEq (Eventually.of_forall fun s => by simp [form]))
    exact hB.trans ((closed z hz).trans hA.symm)
  obtain ⟨h,dh⟩ := conv.exists_forall_hasFDerivAt_of_fderiv_symmetric op
    (fun z hz => ((sf z hz).differentiableAt (by simp)).differentiableWithinAt) symm
  refine ⟨h,fun z hz => ⟨?_,dh z hz⟩⟩
  apply contDiffAt_infty.mpr
  intro n
  cases n with
  | zero => exact contDiffAt_zero.mpr ⟨U,op.mem_nhds hz,fun w hw => (dh w hw).continuousAt.continuousWithinAt⟩
  | succ n =>
    apply (contDiffAt_succ_iff_hasFDerivAt (n:=n)).mpr
    exact ⟨form,⟨U,op.mem_nhds hz,dh⟩,(sf z hz).of_le (by simp)⟩

/-- The first coordinate and its actual conjugate put a smooth positive
metric into isothermal form on an open neighborhood. A scalar harmonic
coordinate is enough; the conjugate and its inverse chart are constructed. -/
theorem isothermal_from_one_harmonic_coordinate {U : Set ℂ} (op : IsOpen U) (conv : Convex ℝ U)
    (E F G : ℂ → ℝ)
    (regular : ∀ z∈U, ContDiffAt ℝ ∞ E z ∧ ContDiffAt ℝ ∞ F z ∧ ContDiffAt ℝ ∞ G z ∧
      0<E z ∧ (F z)^2<E z*G z) (harmonic : ∀ z∈U, FirstCoordinateMetricHarmonicAt E F G z)
    {p : ℂ} (hp : p∈U) :
    ∃ k : OpenPartialHomeomorph ℂ ℂ, p∈k.source ∧ k.source⊆U ∧
      ∀ w∈k.target, ContDiffAt ℝ ∞ k.symm w ∧ ∃ c : ℝ, 0<c ∧ ∀ v : ℂ,
        let q := k.symm w
        let V := fderiv ℝ k.symm w v
        E q*V.re^2+2*F q*V.re*V.im+G q*V.im^2=c*normSq v := by
  let W := planeMetricArea E F G
  let a := fun z => F z/W z
  let b := fun z => G z/W z
  have pos (z : ℂ) (hz : z∈U) : 0<W z := Real.sqrt_pos.mpr (sub_pos.mpr (regular z hz).2.2.2.2)
  have gpos (z : ℂ) (hz : z∈U) : 0<G z :=
    pos_of_mul_pos_right ((sq_nonneg (F z)).trans_lt (regular z hz).2.2.2.2) (regular z hz).2.2.2.1.le
  have sw (z : ℂ) (hz : z∈U) : ContDiffAt ℝ ∞ W z :=
    (((regular z hz).1.mul (regular z hz).2.2.1).sub ((regular z hz).2.1.pow 2)).sqrt
      (sub_pos.mpr (regular z hz).2.2.2.2).ne'
  obtain ⟨η,η_data⟩ := smooth_plane_primitive op conv
    (fun z hz => (show ContDiffAt ℝ ∞ a z from (regular z hz).2.1.div (sw z hz) (pos z hz).ne'))
    (fun z hz => (show ContDiffAt ℝ ∞ b z from (regular z hz).2.2.1.div (sw z hz) (pos z hz).ne')) harmonic
  let f := graphHorizontalChart η
  have sf (z : ℂ) (hz : z∈U) : ContDiffAt ℝ ∞ f z := graphHorizontalChart_contDiffAt (η_data z hz).1
  let D := fun z (hz : z∈U) => (LinearEquiv.ofBijective (graphHorizontalDerivative (a z) (b z)).toLinearMap
    (graphHorizontalDerivative_bijective _ _ (div_pos (gpos z hz) (pos z hz)))).toContinuousLinearEquiv
  have df (z : ℂ) (hz : z∈U) : HasFDerivAt f ((D z hz : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) z :=
    graphHorizontalChart_hasFDerivAt (η_data z hz).2
  let e := (sf p hp).toOpenPartialHomeomorph f (df p hp) (by simp)
  let k := (OpenPartialHomeomorph.ofSet U op).trans e
  have atp : p∈e.source := (sf p hp).mem_toOpenPartialHomeomorph_source (df p hp) (by simp)
  refine ⟨k,⟨hp,atp⟩,fun z hz => hz.1,?_⟩
  intro w hw
  have hq : e.symm w∈U := hw.2
  have inv : ContDiffAt ℝ ∞ e.symm w := e.contDiffAt_symm hw.1 (df _ hq) (sf _ hq)
  let q := e.symm w
  refine ⟨inv,W q^2/G q,div_pos (sq_pos_of_pos (pos q hq)) (gpos q hq),?_⟩
  intro v
  let V := fderiv ℝ e.symm w v
  have rid := openPartialHomeomorph_deriv_right_inverse e hw.1 ((sf q hq).differentiableAt (by simp))
    (inv.differentiableAt (by simp)) v
  change fderiv ℝ f q V=v at rid
  rw [(df q hq).fderiv] at rid
  have components : (⟨V.re,a q*V.re+b q*V.im⟩:ℂ)=v := rid
  change E q*V.re^2+2*F q*V.re*V.im+G q*V.im^2=W q^2/G q*normSq v
  rw [← components]
  simp only [normSq_apply]
  change _=W q^2/G q*(V.re*V.re+(F q/W q*V.re+G q/W q*V.im)*(F q/W q*V.re+G q/W q*V.im))
  have sq : W q^2=E q*G q-F q^2 := Real.sq_sqrt (sub_pos.mpr (regular q hq).2.2.2.2).le
  field_simp [(pos q hq).ne',(gpos q hq).ne']
  nlinarith only [sq,congrArg (fun x : ℝ => (V.re)^2*x) sq,
    congrArg (fun x : ℝ => (V.re)^2*(W q)^2*x) sq]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_plane_primitive
#print axioms TwoAxisHelicoid.isothermal_from_one_harmonic_coordinate

