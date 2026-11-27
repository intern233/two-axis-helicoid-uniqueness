import TwoAxisHelicoid.RegularPlaneContainment
import TwoAxisHelicoid.PeriodicHeightRigidity
import TwoAxisHelicoid.AxisHelicoidGauge
import TwoAxisHelicoid.HoffmanWhiteWindingReduction
import TwoAxisHelicoid.OriginalHandleTopology
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Convex.Contractible

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff

private noncomputable def rulingPhase (g : ℂ) (α b : ℝ) (h : ℝ) : ℂ :=
  g*Complex.exp (I*(α*(h-b):ℝ))

private theorem analytic_rulingPhase (g : ℂ) (α b h : ℝ) : AnalyticAt ℝ (rulingPhase g α b) h := by
  have ha : AnalyticAt ℝ (fun u : ℝ => α*(u-b)) h := analyticAt_const.mul (analyticAt_id.sub analyticAt_const)
  have hz : AnalyticAt ℝ (fun u : ℝ => I*(α*(u-b):ℝ)) h :=
    analyticAt_const.mul ((ofRealCLM.analyticAt _).comp ha)
  exact analyticAt_const.mul ((analyticAt_cexp.restrictScalars (𝕜 := ℝ)).comp hz)

private noncomputable def rulingInverse (g : ℂ) (α b : ℝ) (P : Fin 3 → ℝ) : ℂ :=
  let v := rulingPhase g α b (P 2)
  ((P 0*v.im-P 1*v.re:ℝ):ℂ)+(P 2:ℂ)*I

private theorem rulingInverse_left {g : ℂ} (hg : normSq g=1) (α b : ℝ) :
    Function.LeftInverse (rulingInverse g α b) (axisRuledHelicoid g α b) := by
  intro z
  let v := rulingPhase g α b z.im
  have hv : v.re*v.re+v.im*v.im=1 := by
    change normSq v = 1
    have e : v = g * Complex.exp ((α*(z.im-b) : ℝ)*I) := by dsimp [v,rulingPhase]; rw [mul_comm I]
    rw [e,Complex.normSq_mul,hg,Complex.normSq_eq_norm_sq,Complex.norm_exp_ofReal_mul_I]
    norm_num
  change ((z.re*v.im*v.im-(-z.re*v.re)*v.re : ℝ):ℂ)+(z.im:ℂ)*I = z
  apply Complex.ext
  · simp only [Complex.add_re,Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_re,
      Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero]
    linear_combination z.re*hv
  · simp

private theorem rulingInverse_analytic (g : ℂ) (α b : ℝ) (P : Fin 3 → ℝ) :
    AnalyticAt ℝ (rulingInverse g α b) P := by
  have hp (j : Fin 3) : AnalyticAt ℝ (fun Q : Fin 3 → ℝ => Q j) P := (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).analyticAt _
  have hv := (analytic_rulingPhase g α b (P 2)).comp (f := fun Q : Fin 3 → ℝ => Q 2) (hp 2)
  have h := ((hp 0).mul ((imCLM.analyticAt _).comp hv)).sub ((hp 1).mul ((reCLM.analyticAt _).comp hv))
  exact ((ofRealCLM.analyticAt _).comp h).add (((ofRealCLM.analyticAt _).comp (hp 2)).mul analyticAt_const)

private theorem axisRuledHelicoid_analytic (g : ℂ) (α b : ℝ) (z : ℂ) :
    AnalyticAt ℝ (axisRuledHelicoid g α b) z := by
  have hv := (analytic_rulingPhase g α b z.im).comp (imCLM.analyticAt z)
  apply analyticAt_pi_iff.mpr
  intro j
  fin_cases j
  · exact (reCLM.analyticAt z).mul ((imCLM.analyticAt _).comp hv)
  · exact (reCLM.analyticAt z).neg.mul ((reCLM.analyticAt _).comp hv)
  · exact imCLM.analyticAt z

theorem axisHelicoidSide_analytic (g : ℂ) (α b : ℝ) (P : Fin 3 → ℝ) : AnalyticAt ℝ (axisHelicoidSide g α b) P := by
  have hp (j : Fin 3) : AnalyticAt ℝ (fun Q : Fin 3 → ℝ => Q j) P := (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).analyticAt _
  have hv := (analytic_rulingPhase g α b (P 2)).comp (f := fun Q : Fin 3 → ℝ => Q 2) (hp 2)
  exact (((reCLM.analyticAt _).comp hv).mul (hp 0)).add (((imCLM.analyticAt _).comp hv).mul (hp 1))

/-- No patch of a closed embedded harmonic punctured torus agrees with a
ruled comparison helicoid. Analytic continuation, the derivative rank and
the nontrivial fundamental group of the punctured torus prove this directly. -/
theorem marked_torus_not_locally_contained_in_helicoid
    {L : PeriodPair} {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion L X)
    (hE : IsClosedEmbedding (harmonicTorusImmersion hX))
    {g : ℂ} (hg : normSq g = 1) (α b : ℝ) {z : ℂ} (hz : z ∉ L.lattice) :
    ¬ ∀ᶠ w in 𝓝 z, X w ∈ range (axisRuledHelicoid g α b) := by
  intro hnear
  have hpos : AnalyticOnNhd ℝ X (L.lattice : Set ℂ)ᶜ :=
    fun w hw => analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (hX.harmonic w hw j)
  have hi : ContDiff ℝ 1 (axisRuledHelicoid g α b) := contDiff_iff_contDiffAt.mpr fun w => (axisRuledHelicoid_analytic g α b w).contDiffAt
  have hj : ContDiff ℝ 1 (rulingInverse g α b) := contDiff_iff_contDiffAt.mpr fun p => (rulingInverse_analytic g α b p).contDiffAt
  have im := harmonicTorusImmersion_range hX
  have eq := analytically_contained_regular_surface_image L.isClosed_lattice.isOpen_compl
    (marked_torus_lattice_complement_connected L).isPreconnected hz X hpos hX.immersion
    (im ▸ hE.isClosed_range) _ _ hi hj (rulingInverse_left hg α b) _
    (axisHelicoidSide_analytic g α b) (axisHelicoidSide_eq_zero_iff hg α b) hnear
  have emb := (rulingInverse_left hg α b).isEmbedding hj.continuous hi.continuous
  let home := (hE.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr (im.trans eq))).trans emb.toHomeomorph.symm
  exact punctured_period_torus_not_simply_connected L home.toHomotopyEquiv.simplyConnectedSpace

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_torus_not_locally_contained_in_helicoid
