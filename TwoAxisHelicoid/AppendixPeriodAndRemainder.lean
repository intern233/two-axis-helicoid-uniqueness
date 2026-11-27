import TwoAxisHelicoid.ActualMarkedHeightNormalization
import TwoAxisHelicoid.ManuscriptJacobiRemainder

namespace TwoAxisHelicoid
open Complex Set Filter Asymptotics
open scoped Topology

/-- The second *actual* marked period in Appendix C.1, after the real
period of the first generator has been set to zero. The zeta values
are full increments, and s is recovered from the first period. -/
theorem actual_second_marked_period_real_part (τ : ℂ) (upper : 0<τ.im) (A : ℂ) {f g : ℂ → ℂ}
    (an : ∀ z∉(upperMarkedLattice τ upper).lattice, DifferentiableAt ℂ f z)
    (periodic : ∀ z w, w∈(upperMarkedLattice τ upper).lattice → f (z+w)=f z)
    (regular : AnalyticAt ℂ g 0)
    (principal : ∀ᶠ z in 𝓝 (0:ℂ), z≠0 → f z=A/z^2+g z)
    (q : PuncturedPeriodTorus (upperMarkedLattice τ upper))
    (closed : ∀ (γ : Path q q) (v : ℂ), TorusPathIntegral (upperMarkedLattice τ upper) f γ v → v.re=0) :
    let L := upperMarkedLattice τ upper
    let P := g 0-A*markedZetaIncrement L 1
    let s := P.im
    let V := 2*(Real.pi:ℂ)*I*A+I*(s:ℂ)*τ
    P=I*(s:ℂ) ∧ markedHeightCharacter L A (g 0) ⟨L.ω₂,L.ω₂_mem_lattice⟩=V ∧
      (∃ γ : Path q q, TorusPathIntegral L f γ V) ∧ 0=V.re ∧
      V.re= -2*Real.pi*A.im-s*τ.im ∧ s= -2*Real.pi*A.im/τ.im := by
  let L := upperMarkedLattice τ upper
  let B := g 0
  let P := B-A*markedZetaIncrement L 1
  let s := P.im
  let V := 2*(Real.pi:ℂ)*I*A+I*(s:ℂ)*τ
  have coeff := elliptic_double_pole_classification L A an periodic regular principal
  have loop (w : L.lattice) : ∃ γ : Path q q, TorusPathIntegral L f γ (markedHeightCharacter L A B w) :=
    (marked_double_pole_actual_loop_periods L A B an periodic coeff q _).mpr ⟨w,rfl⟩
  have hP : P.re=0 := by
    obtain ⟨γ,hγ⟩ := loop ⟨L.ω₁,L.ω₁_mem_lattice⟩
    have h := closed γ _ hγ
    change (B*1-A*markedZetaIncrement L 1).re=0 at h
    simpa only [P,mul_one] using h
  have first : P=I*(s:ℂ) := by
    calc P = (P.re:ℂ)+(P.im:ℂ)*I := (Complex.re_add_im P).symm
         _ = _ := by rw [hP,Complex.ofReal_zero,zero_add]; exact mul_comm _ _
  have second : markedHeightCharacter L A B ⟨L.ω₂,L.ω₂_mem_lattice⟩=V := by
    have relation := marked_height_period_relation τ _ _ A B (marked_full_quasiperiod_legendre τ upper)
    change B*τ-A*markedZetaIncrement L τ=P*τ+2*(Real.pi:ℂ)*I*A at relation
    change B*τ-A*markedZetaIncrement L τ=V
    rw [relation,first]
    exact add_comm _ _
  obtain ⟨γ,hγ⟩ := loop ⟨L.ω₂,L.ω₂_mem_lattice⟩
  rw [second] at hγ
  have zero := closed γ V hγ
  have realPart : V.re= -2*Real.pi*A.im-s*τ.im := by
    simp [V,Complex.add_re,Complex.mul_re,Complex.mul_im]
    ring
  refine ⟨first,second,⟨γ,hγ⟩,zero.symm,realPart,?_⟩
  exact (eq_div_iff upper.ne').mpr (by linarith)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_second_marked_period_real_part
