import TwoAxisHelicoid.HelicoidInteriorCrossing

namespace TwoAxisHelicoid
open Complex Filter Set Topology
open scoped Topology

/-- Normal direction at height zero for the leaf with horizontal
ruling of angle k. -/
noncomputable def helicoidPhaseNormal (k : ℝ) : ℂ := I * exp ((k:ℂ)*I)

theorem helicoidPhaseNormal_unit (k : ℝ) : normSq (helicoidPhaseNormal k)=1 := by
  simp [helicoidPhaseNormal,normSq_eq_norm_sq]

/-- In polar coordinates, the signed equation of the comparison leaf
is exactly the horizontal radius times the sine of its phase difference. -/
theorem axisHelicoidSide_polar (p : Fin 3 → ℝ) (k α b r θ : ℝ)
    (hx : p 0=r*Real.cos θ) (hy : p 1=r*Real.sin θ) :
    axisHelicoidSide (helicoidPhaseNormal k) α b p = r*Real.sin ((θ-α*(p 2-b))-k) := by
  let h := α*(p 2-b)
  have e : helicoidPhaseNormal k * exp (I*(h:ℂ))=I*exp (((k+h:ℝ):ℂ)*I) := by
    unfold helicoidPhaseNormal
    rw [mul_assoc,← Complex.exp_add]
    push_cast
    ring_nf
  change (helicoidPhaseNormal k * exp (I*(h:ℂ))).re * p 0 +
    (helicoidPhaseNormal k * exp (I*(h:ℂ))).im * p 1 = r*Real.sin ((θ-h)-k)
  rw [e,Complex.I_mul_re,Complex.I_mul_im,exp_ofReal_mul_I_im,exp_ofReal_mul_I_re,hx,hy,
    show θ-h-k=θ-(k+h) by ring,Real.sin_sub]
  ring

/-- Any continuous choice of horizontal angle off the vertical axis
gives a helicoidal phase with neither an interior maximum nor an
interior minimum on the embedded marked torus. -/
theorem marked_torus_phase_no_interior_extremum {L : PeriodPair} {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion L X) (hE : IsClosedEmbedding (harmonicTorusImmersion hX))
    {z : ℂ} (hz : z ∉ L.lattice) {r θ : ℂ → ℝ} (ct : ContinuousAt θ z) (α b : ℝ)
    (polar : ∀ᶠ w in 𝓝 z, 0 < r w ∧ X w 0=r w*Real.cos (θ w) ∧ X w 1=r w*Real.sin (θ w)) :
    ¬IsLocalExtr (fun w => θ w-α*(X w 2-b)) z := by
  let F := fun w => θ w-α*(X w 2-b)
  let g := helicoidPhaseNormal (F z)
  have unit : normSq g=1 := helicoidPhaseNormal_unit _
  have cs := (continuous_apply (2 : Fin 3)).continuousAt.comp (hX.differentiable z hz).continuousAt
  have cf : ContinuousAt F z := ct.sub (continuousAt_const.mul (cs.sub continuousAt_const))
  have form : ∀ᶠ w in 𝓝 z, axisHelicoidSide g α b (X w) = r w*Real.sin (F w-F z) :=
    polar.mono fun w hw => axisHelicoidSide_polar _ _ _ _ _ _ hw.2.1 hw.2.2
  have on : X z ∈ range (axisRuledHelicoid g α b) := by
    apply (axisHelicoidSide_eq_zero_iff unit α b _).mp
    simpa only [sub_self,Real.sin_zero,mul_zero] using form.self_of_nhds
  obtain ⟨pos,neg⟩ := marked_torus_crosses_comparison_helicoid hX hE unit α b hz on
  have close : ∀ᶠ w in 𝓝 z, |F w-F z|<Real.pi := by
    have c : ContinuousAt (fun w => |F w-F z|) z := (cf.sub continuousAt_const).abs
    exact c.eventually_lt continuousAt_const (by simpa using Real.pi_pos)
  rintro (lo | hi)
  · apply neg
    filter_upwards [lo,form,polar,close] with w ge eq p bound
    have h₀ : F z ≤ F w := ge
    rw [eq]
    exact not_lt_of_ge (mul_nonneg p.1.le (Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr h₀) (abs_lt.mp bound).2.le))
  · apply pos
    filter_upwards [hi,form,polar,close] with w le eq p bound
    have h₀ : F w ≤ F z := le
    rw [eq]
    exact not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos p.1.le (Real.sin_nonpos_of_nonpos_of_neg_pi_le (sub_nonpos.mpr h₀) (abs_lt.mp bound).1.le))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.axisHelicoidSide_polar
#print axioms TwoAxisHelicoid.marked_torus_phase_no_interior_extremum
