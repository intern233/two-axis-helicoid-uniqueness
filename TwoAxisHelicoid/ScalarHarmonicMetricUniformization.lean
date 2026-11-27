import TwoAxisHelicoid.PublishedIsothermalHandleSpin
import TwoAxisHelicoid.PlaneMetricHarmonicCoframe

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology
open scoped Topology Manifold ContDiff
set_option maxHeartbeats 2000000
universe u v

/-- Given a plane metric and a scalar field, these are the two coefficients
of its rotated differential. -/
noncomputable def metricConjugateFirst (E F G : ℂ → ℝ) (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  (F z*fderiv ℝ u z 1-E z*fderiv ℝ u z I)/planeMetricArea E F G z

noncomputable def metricConjugateSecond (E F G : ℂ → ℝ) (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  (G z*fderiv ℝ u z 1-F z*fderiv ℝ u z I)/planeMetricArea E F G z

/-- The scalar divergence-form Laplace–Beltrami equation with one prescribed
gradient on a small disk. No coordinate, inverse, or conjugate is given. -/
def LocalMetricHarmonicScalarExists : Prop :=
  ∀ (U : Set ℂ), IsOpen U → ∀ E F G : ℂ → ℝ,
    (∀ z∈U, ContDiffAt ℝ ∞ E z ∧ ContDiffAt ℝ ∞ F z ∧ ContDiffAt ℝ ∞ G z ∧
      0<E z ∧ (F z)^2<E z*G z) →
    ∀ p∈U, ∃ (r : ℝ) (u : ℂ → ℝ), 0<r ∧ ball p r⊆U ∧ fderiv ℝ u p 1=1 ∧
      ∀ z∈ball p r, ContDiffAt ℝ ∞ u z ∧
        fderiv ℝ (metricConjugateSecond E F G u) z 1 = fderiv ℝ (metricConjugateFirst E F G u) z I

/-- Starting with a solution of just one scalar elliptic equation, construct
both smooth coordinates, their inverse and the pullback metric factor. -/
theorem isothermal_coordinates_of_scalar_harmonic_existence (solve : LocalMetricHarmonicScalarExists) :
    LocalSmoothMetricIsothermalCoordinates := by
  intro U op E F G smooth p hp
  obtain ⟨r,u,rp,region,first,harm⟩ := solve U op E F G smooth p hp
  let B := ball p r
  let ux := fun z => fderiv ℝ u z 1
  let uy := fun z => fderiv ℝ u z I
  have up : p∈B := mem_ball_self rp
  have sd (z : ℂ) (hz : z∈B) (v : ℂ) : ContDiffAt ℝ ∞ (fun t => fderiv ℝ u t v) z :=
    ((harm z hz).1.fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const
  have positive : 0<ux p := by change 0<fderiv ℝ u p 1; rw [first]; norm_num
  have inBall : ∀ᶠ z in 𝓝 p, z∈B := isOpen_ball.mem_nhds up
  have posNearby : ∀ᶠ z in 𝓝 p, 0<ux z := (sd p up 1).continuousAt.eventually (Ioi_mem_nhds positive)
  have near := inBall.and posNearby
  obtain ⟨s,sp,inc⟩ := Metric.mem_nhds_iff.mp near
  let V := ball p s
  have pv : p∈V := mem_ball_self sp
  have vb {z : ℂ} (hz : z∈V) : z∈B := (inc hz).1
  have nz {z : ℂ} (hz : z∈V) : ux z≠0 := (inc hz).2.ne'
  let W := planeMetricArea E F G
  let a := metricConjugateFirst E F G u
  let b := metricConjugateSecond E F G u
  let H := fun z => G z*(ux z)^2-2*F z*ux z*uy z+E z*(uy z)^2
  have area {z : ℂ} (hz : z∈V) : 0<W z := Real.sqrt_pos.mpr (sub_pos.mpr (smooth z (region (vb hz))).2.2.2.2)
  have dual {z : ℂ} (hz : z∈V) : 0<H z := plane_metric_dual_numerator_pos
    (smooth z (region (vb hz))).2.2.2.1 (smooth z (region (vb hz))).2.2.2.2 (nz hz)
  have stars (z : ℂ) (hz : z∈V) : ContDiffAt ℝ ∞ a z ∧ ContDiffAt ℝ ∞ b z := by
    obtain ⟨se,sf,sg,_,dt⟩ := smooth z (region (vb hz))
    have sw : ContDiffAt ℝ ∞ W z := ((se.mul sg).sub (sf.pow 2)).sqrt (sub_pos.mpr dt).ne'
    have sx := sd z (vb hz) 1
    have sy := sd z (vb hz) I
    exact ⟨((sf.mul sx).sub (se.mul sy)).div sw (area hz).ne',((sg.mul sx).sub (sf.mul sy)).div sw (area hz).ne'⟩
  obtain ⟨η,dη⟩ := smooth_plane_primitive isOpen_ball (convex_ball p s)
    (fun z hz => (stars z hz).1) (fun z hz => (stars z hz).2) (fun z hz => (harm z (vb hz)).2)
  let f := fun z => equivRealProdCLM.symm (u z,η z)
  let T := fun z => equivRealProdCLM.symm.toContinuousLinearMap.comp
    ((fderiv ℝ u z).prod (a z • reCLM+b z • imCLM))
  have coordinate (z v : ℂ) : T z v=⟨ux z*v.re+uy z*v.im,a z*v.re+b z*v.im⟩ := by
    apply Complex.ext
    · change fderiv ℝ u z v=_
      rw [real_linear_complex_expansion (fderiv ℝ u z) v]
      change v.re*ux z+v.im*uy z=_
      ring
    · rfl
  have bij (z : ℂ) (hz : z∈V) : Function.Bijective (T z) := by
    apply plane_coframe_bijective _ _ _ _ _ (coordinate z)
    have eq : ux z*b z-uy z*a z=H z/W z := by dsimp [a,b,H,ux,uy,W,metricConjugateFirst,metricConjugateSecond]; ring
    exact eq ▸ (div_pos (dual hz) (area hz)).ne'
  have sf (z : ℂ) (hz : z∈V) : ContDiffAt ℝ ∞ f z :=
    equivRealProdCLM.symm.contDiff.contDiffAt.comp z ((harm z (vb hz)).1.prodMk (dη z hz).1)
  let D := fun z (hz : z∈V) => (LinearEquiv.ofBijective (T z).toLinearMap (bij z hz)).toContinuousLinearEquiv
  have df (z : ℂ) (hz : z∈V) : HasFDerivAt f ((D z hz : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) z :=
    equivRealProdCLM.symm.hasFDerivAt.comp z (((harm z (vb hz)).1.differentiableAt (by simp)).hasFDerivAt.prodMk (dη z hz).2)
  let e := (sf p pv).toOpenPartialHomeomorph f (df p pv) (by simp)
  let k := (OpenPartialHomeomorph.ofSet V isOpen_ball).trans e
  have atp : p∈e.source := (sf p pv).mem_toOpenPartialHomeomorph_source (df p pv) (by simp)
  refine ⟨k,⟨pv,atp⟩,fun z hz => region (vb hz.1),?_⟩
  intro w hw
  let q := e.symm w
  have hq : q∈V := hw.2
  have inv : ContDiffAt ℝ ∞ e.symm w := e.contDiffAt_symm hw.1 (df _ hq) (sf _ hq)
  refine ⟨inv,W q^2/H q,div_pos (sq_pos_of_pos (area hq)) (dual hq),?_⟩
  intro v
  let X := fderiv ℝ e.symm w v
  have rid := openPartialHomeomorph_deriv_right_inverse e hw.1 ((sf q hq).differentiableAt (by simp))
    (inv.differentiableAt (by simp)) v
  change fderiv ℝ f q X=v at rid
  rw [(df q hq).fderiv] at rid
  have value := (coordinate q X).symm.trans rid
  change E q*X.re^2+2*F q*X.re*X.im+G q*X.im^2=W q^2/H q*normSq v
  rw [← value]
  have sq : W q^2=E q*G q-F q^2 := Real.sq_sqrt (sub_pos.mpr (smooth q (region (vb hq))).2.2.2.2).le
  simpa only [H,a,b,ux,uy,W,metricConjugateFirst,metricConjugateSecond,normSq_apply,pow_two] using
    plane_metric_conjugate_coframe (p:=ux q) (q:=uy q) (area hq) sq (dual hq).ne' X.re X.im

/-- The general, nonminimal height-end spin extension now has a single
local scalar PDE as its only external mathematical input. -/
theorem prescribed_handle_spin_of_scalar_elliptic_existence (solve : LocalMetricHarmonicScalarExists)
    {M : Type v} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M]
    {L : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L) (X : M → Fin 3 → ℝ) (cl : IsClosedEmbedding X)
    (sm : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X)
    (di : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X x))
    (A : (Fin 3 → ℝ) ≃ₜ HelicoidTubeCoordinates) (sa : ContDiff ℝ ∞ A) (si : ContDiff ℝ ∞ A.symm)
    (height : HasHelicoidHeightEnd (A ∘ X)) :
    ∃ e : Diffeomorph 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) M (PuncturedPeriodTorus L) ∞, EvenSpinExtensionInMarking.{u} X e :=
  prescribed_handle_spin_of_local_isothermal_theorem (isothermal_coordinates_of_scalar_harmonic_existence solve)
    top X cl sm di A sa si height
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.isothermal_coordinates_of_scalar_harmonic_existence
#print axioms TwoAxisHelicoid.prescribed_handle_spin_of_scalar_elliptic_existence

