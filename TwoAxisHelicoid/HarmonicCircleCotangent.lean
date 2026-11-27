import TwoAxisHelicoid.HolomorphicDiskSectionExtension
import TwoAxisHelicoid.PlaneOrientationCircleDegree
import TwoAxisHelicoid.HolomorphicImmersionCoordinateChange

namespace TwoAxisHelicoid
open Complex Set Filter Topology Metric InnerProductSpace
open scoped Topology ContDiff Manifold

/-- Real local lifts of the same circle phase have identical first derivatives. -/
theorem real_circle_lifts_same_differential {F G : ℂ → ℝ} {z : ℂ}
    (hf : DifferentiableAt ℝ F z) (hg : DifferentiableAt ℝ G z)
    (phase : ∀ᶠ w in 𝓝 z, (F w : OrientationCircle)=(G w : OrientationCircle)) :
    scalarComplexCoefficient F z=scalarComplexCoefficient G z := by
  have integral {a b : ℝ} (h : (a : OrientationCircle)=(b : OrientationCircle)) : ∃ n : ℤ, a-b=(n:ℝ) := by
    have zero : ((a-b:ℝ):OrientationCircle)=0 := by rw [AddCircle.coe_sub,h,sub_self]
    obtain ⟨n,hn⟩ := (AddCircle.coe_eq_zero_iff (1:ℝ)).mp zero
    exact ⟨n,by simpa using hn.symm⟩
  obtain ⟨m,at0⟩ := integral phase.self_of_nhds
  have c : ContinuousAt (fun w => F w-G w) z := hf.continuousAt.sub hg.continuousAt
  have same : F =ᶠ[𝓝 z] fun w => G w+(m:ℝ) := by
    filter_upwards [phase,c.eventually (ball_mem_nhds (F z-G z) one_pos)] with w hw near
    obtain ⟨n,atw⟩ := integral hw
    change dist (F w-G w) (F z-G z)<1 at near
    rw [Real.dist_eq,atw,at0] at near
    have ni : |n-m|<(1:ℤ) := by exact_mod_cast near
    have eq := sub_eq_zero.mp (Int.abs_lt_one_iff.mp ni)
    linarith [congrArg (fun v : ℤ => (v:ℝ)) eq]
  have eq : fderiv ℝ F z=fderiv ℝ G z := same.fderiv_eq.trans (hg.hasFDerivAt.add_const (m:ℝ)).fderiv
  simp only [scalarComplexCoefficient,eq]

/-- Local lifts of a circle-valued function are harmonic in the
preferred conformal coordinates. The lifts may have nonzero periods. -/
def HasLocalHarmonicArguments {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (φ : M → OrientationCircle) : Prop := ∀ x : M, ∃ u : ℂ → ℝ, HarmonicAt u (chartAt ℂ x x) ∧
      ∀ᶠ z in 𝓝 (chartAt ℂ x x), (u z : OrientationCircle)=φ ((chartAt ℂ x).symm z)

/-- A harmonic phase of nontrivial homotopy class yields an actual
nonzero global holomorphic one-form in the given complex structure. -/
theorem harmonic_nonliftable_phase_gives_holomorphic_section {M : Type*} [TopologicalSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] [PreconnectedSpace M] {φ : M → OrientationCircle}
    (harmonic : HasLocalHarmonicArguments φ) (essential : ¬∃ g : C(M,ℝ), ∀ x, (g x : OrientationCircle)=φ x) :
    ∃ w : holomorphicCotangentSections M, w≠0 := by
  classical
  choose U harm phase using harmonic
  have disk (i : M) : ∃ r : ℝ, 0<r ∧ ∀ z∈ball (chartAt ℂ i i) r, z∈(chartAt ℂ i).target ∧
      HarmonicAt (U i) z ∧ (U i z : OrientationCircle)=φ ((chartAt ℂ i).symm z) := by
    have target := (chartAt ℂ i).open_target.mem_nhds ((chartAt ℂ i).map_source (mem_chart_source ℂ i))
    have all : ∀ᶠ z in 𝓝 (chartAt ℂ i i), z∈(chartAt ℂ i).target ∧
        HarmonicAt (U i) z ∧ (U i z : OrientationCircle)=φ ((chartAt ℂ i).symm z) := by
      filter_upwards [target,(isOpen_setOfPred_harmonicAt (f := U i)).mem_nhds (harm i),phase i] with z h t p
      exact ⟨h,t,p⟩
    exact Metric.mem_nhds_iff.mp all
  choose r positive properties using disk
  let A : HolomorphicCoefficientDisks M := ⟨r,positive,fun i z hz => (properties i z hz).1,
    fun i => scalarComplexCoefficient (U i),fun i z hz => scalarComplexCoefficient_analyticAt (properties i z hz).2.1⟩
  have comp : A.compatibleOneForm := by
    intro i j x hx
    let e := chartAt ℂ i
    let b := chartAt ℂ j
    let z := e x
    let f := b ∘ e.symm
    have atz : f z=b x := congrArg b (e.left_inv hx.1.1)
    have tr : AnalyticAt ℂ f z := (complexAtlas_realized_transition
      (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ i)) (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ j))
      (planeChart_transition_source hx.1.1 hx.2.1)).analyticAt
    have hu := (_root_.HarmonicAt.analyticAt (properties i z hx.1.2).2.1).differentiableAt
    have hv : DifferentiableAt ℝ (U j) (f z) := atz ▸ (_root_.HarmonicAt.analyticAt (properties j _ hx.2.2).2.1).differentiableAt
    have same : ∀ᶠ w in 𝓝 z, (U i w : OrientationCircle)=(U j (f w) : OrientationCircle) := by
      have through : e.symm z∈A.primitives.domain j := (e.left_inv hx.1.1).symm ▸ hx.2
      filter_upwards [isOpen_ball.mem_nhds hx.1.2,(e.symm.continuousAt (e.map_source hx.1.1)).eventually
        ((A.primitives.domain_isOpen j).mem_nhds through)] with w hw inside
      have l := (properties i w hw).2.2
      have g := (properties j (f w) inside.2).2.2
      change (U j (f w) : OrientationCircle)=φ (b.symm (b (e.symm w))) at g
      exact l.trans (by simpa only [b.left_inv inside.1] using g.symm)
    have eq := real_circle_lifts_same_differential hu (hv.comp z (tr.differentiableAt.restrictScalars ℝ)) same
    have vector : DifferentiableAt ℝ (fun v : ℂ => fun _ : Fin 3 => U j v) (f z) :=
      differentiableAt_pi.mpr fun _ => hv
    have chain := immersionComplexCoefficient_comp_holomorphic vector tr.differentiableAt.hasDerivAt (0:Fin 3)
    change scalarComplexCoefficient (U j ∘ f) z=deriv f z*scalarComplexCoefficient (U j) (f z) at chain
    rw [atz,mul_comm] at chain
    exact eq.trans chain
  obtain ⟨w,agreement⟩ := A.exists_global_section comp
  refine ⟨w,?_⟩
  intro zero
  have flat (i : M) (v : ℂ) (hv : v∈ball (chartAt ℂ i i) (r i)) : fderiv ℝ (U i) v=0 := by
    have tar := (properties i v hv).1
    let x := (chartAt ℂ i).symm v
    have val : chartAt ℂ i x=v := (chartAt ℂ i).right_inv tar
    have dom : x∈A.primitives.domain i := ⟨(chartAt ℂ i).map_target tar,by change chartAt ℂ i x∈ball (chartAt ℂ i i) (r i); rwa [val]⟩
    have coeff := agreement i x dom
    rw [zero,val] at coeff
    change 0=scalarComplexCoefficient (U i) v at coeff
    rw [(scalarComplexCoefficient_hasFDerivAt (_root_.HarmonicAt.analyticAt (properties i v hv).2.1).differentiableAt).fderiv,← coeff]
    ext d
    simp [realCoefficientDerivative]
  have lc : IsLocallyConstant φ := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro i
    have one {u v : ℂ} (hu : u∈ball (chartAt ℂ i i) (r i)) (hv : v∈ball (chartAt ℂ i i) (r i)) : U i u=U i v :=
      isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball (chartAt ℂ i i) (r i)).isPreconnected
      (fun z hz => (_root_.HarmonicAt.analyticAt (properties i z hz).2.1).differentiableAt.differentiableWithinAt)
      (fun z hz => flat i z hz) hu hv
    have ci := (properties i _ (mem_ball_self (positive i))).2.2
    rw [(chartAt ℂ i).left_inv (mem_chart_source ℂ i)] at ci
    filter_upwards [(A.primitives.domain_isOpen i).mem_nhds (A.primitives.mem_domain i)] with x hx
    have h := (properties i _ hx.2).2.2
    rw [(chartAt ℂ i).left_inv hx.1,one hx.2 (mem_ball_self (positive i)),ci] at h
    exact h.symm
  obtain ⟨c,constant⟩ := lc.exists_eq_const
  obtain ⟨y,hy⟩ := (Quotient.mk_surjective : Function.Surjective ((↑) : ℝ → OrientationCircle)) c
  exact essential ⟨ContinuousMap.const M y,fun x => hy.trans (congrFun constant x).symm⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_nonliftable_phase_gives_holomorphic_section
