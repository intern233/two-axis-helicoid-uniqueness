import TwoAxisHelicoid.DoublePoleGaussLogPatches
import TwoAxisHelicoid.OriginalPoleEndTorusReduction
import TwoAxisHelicoid.NullCoordinateRecognition

namespace TwoAxisHelicoid
open Complex Set Filter Bornology Topology
open scoped Topology ContDiff Manifold

private noncomputable def scaledReciprocal (a : ℂ) (ha : a≠0) : OpenPartialHomeomorph ℂ ℂ where
  toFun z := a/z
  invFun z := a/z
  source := {0}ᶜ
  target := {0}ᶜ
  map_source' := fun _ hz => div_ne_zero ha hz
  map_target' := fun _ hz => div_ne_zero ha hz
  left_inv' := fun z hz => by field_simp
  right_inv' := fun z hz => by field_simp
  open_source := isClosed_singleton.isOpen_compl
  open_target := isClosed_singleton.isOpen_compl
  continuousOn_toFun := fun z hz => (continuousAt_const.div continuousAt_id hz).continuousWithinAt
  continuousOn_invFun := fun z hz => (continuousAt_const.div continuousAt_id hz).continuousWithinAt

private theorem reciprocal_tendsto_puncture {a : ℂ} (ha : a≠0) :
    Tendsto (fun z : ℂ => a/z) (cobounded ℂ) (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_,?_⟩
  · simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := a)).mul (tendsto_inv₀_cobounded (α := ℂ))
  · filter_upwards [eventually_cobounded_le_norm (E := ℂ) (1:ℝ)] with z hz
    exact div_ne_zero ha (fun e => by rw [e,norm_zero] at hz; linarith)

/-- The puncture chart, rescaled and inverted using the actual
logarithmic Gauss pole, has ordinary holomorphic Weierstrass data on
a half-plane. Vertical lines in that half-plane escape all compact
sets of the original surface as their real coordinates increase. -/
theorem geometric_double_pole_gauss_half_plane {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {X : M → Fin 3 → ℝ}
    (charts : ∀ d ∈ atlas ℂ M, HarmonicImmersionChart X d) (A : GeometricDoublePoleEnd X) :
    ∃ (e : OpenPartialHomeomorph M ℂ) (B : ℝ) (W h : ℂ → ℂ),
      e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M ∧ Tendsto e.symm (cobounded ℂ) (cocompact M) ∧
      (∀ z : ℂ, B<z.re → z∈e.target ∧ AnalyticAt ℂ W z ∧ AnalyticAt ℂ h z ∧ h z≠0 ∧
        HasFDerivAt (X ∘ e.symm) (nullRealDerivative (weierstrassTriple (exp (W z)) (h z))) z) ∧
      ∀ δ : ℝ, 0<δ → ∃ D : ℝ, ∀ z : ℂ, D<z.re → AnalyticAt ℂ W z ∧ ‖deriv W z-I‖≤δ := by
  let E := A.endChart
  let Y := X ∘ E.coord.symm
  obtain ⟨a,B,W,ha,_,hw,asym⟩ := double_pole_gauss_log_right_half_plane (G := immersionGaussMap Y) A.gauss A.gaussOrder
  let inv := scaledReciprocal a ha
  let e := E.coord.trans inv
  have hol : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M := by
    apply e.mem_maximalAtlas_of_contMDiffOn
    · intro x hx
      have nz : E.coord x≠0 := hx.2
      have d : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun w : ℂ => a/w) (E.coord x) :=
        contMDiffAt_iff_contDiffAt.mpr (analyticAt_const.div analyticAt_id nz).contDiffAt
      exact (d.comp x (contMDiffAt_of_mem_maximalAtlas A.holomorphic hx.1)).contMDiffWithinAt
    · intro z hz
      have nz : z≠0 := hz.1
      have d : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun w : ℂ => a/w) z :=
        contMDiffAt_iff_contDiffAt.mpr (analyticAt_const.div analyticAt_id nz).contDiffAt
      exact ((contMDiffAt_symm_of_mem_maximalAtlas A.holomorphic hz.2).comp z d).contMDiffWithinAt
  have lim := reciprocal_tendsto_puncture ha
  have tar : ∀ᶠ z in cobounded ℂ, a/z∈E.coord.target := lim.eventually (by
    rw [E.target_eq]
    exact inter_mem (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ E.radius_pos)) self_mem_nhdsWithin)
  let h := fun z => immersionComplexCoefficient (X ∘ e.symm) z 2
  have height := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero A.height).mp (by rw [A.heightOrder]; decide)
  have hm := harmonic_immersion_chart_maximal charts A.holomorphic
  have hm' := harmonic_immersion_chart_maximal charts hol
  obtain ⟨D,_,bound⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (tar.and ((lim.eventually height).and (eventually_cobounded_le_norm (E := ℂ) (1:ℝ))))
  refine ⟨e,max B D,W,h,hol,E.from_zero.comp lim,fun z hz => ?_,asym⟩
  have bh := (le_max_left B D).trans_lt hz
  obtain ⟨target,nh,hnorm⟩ := bound ((le_max_right B D).trans (hz.le.trans (re_le_norm z)))
  have nz : z≠0 := fun e => by rw [e,norm_zero] at hnorm; linarith
  have ze : z∈e.target := ⟨nz,target⟩
  have dx : DifferentiableAt ℝ Y (a/z) := (analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt ((hm _ target).1 j))).differentiableAt
  have d : HasDerivAt (fun w : ℂ => a/w) (-a/z^2) z := by
    simpa only [zero_mul,one_mul,mul_one,zero_sub,id_eq] using! (hasDerivAt_const z a).div (hasDerivAt_id z) nz
  have nd : -a/z^2≠0 := div_ne_zero (neg_ne_zero.mpr ha) (pow_ne_zero _ nz)
  have gh : immersionGaussMap (X ∘ e.symm) z=immersionGaussMap Y (a/z) := immersionGaussMap_comp_holomorphic dx d nd
  have hh : h z= (-a/z^2)*immersionComplexCoefficient Y (a/z) 2 := immersionComplexCoefficient_comp_holomorphic dx d 2
  have nh' : h z≠0 := hh ▸ mul_ne_zero nd nh
  have reg := hm' z ze
  have der := immersionComplexCoefficient_hasFDerivAt
    ((analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt (reg.1 j))).differentiableAt)
  have form := null_eq_weierstrassTriple (immersionComplexCoefficient_null reg.2.1) nh'
  change immersionComplexCoefficient (X ∘ e.symm) z=weierstrassTriple (immersionGaussMap (X ∘ e.symm) z) (h z) at form
  rw [gh,← (hw z bh).2] at form
  exact ⟨ze,(hw z bh).1,scalarComplexCoefficient_analyticAt (reg.1 2),nh',form ▸ der⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.geometric_double_pole_gauss_half_plane
