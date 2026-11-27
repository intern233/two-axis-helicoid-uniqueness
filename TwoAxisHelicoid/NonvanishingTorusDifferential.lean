import TwoAxisHelicoid.TranslationTorusUniformization
import TwoAxisHelicoid.HolomorphicPeriodNormalization
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

namespace TwoAxisHelicoid
open Complex Set Filter Topology Metric
open scoped Topology ContDiff Manifold

namespace HolomorphicCoefficientDisks
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]

/-- The ordinary transformation rule for the coefficients of a
holomorphic one-form on overlapping coordinate disks. -/
def compatibleOneForm (A : HolomorphicCoefficientDisks M) : Prop :=
  ∀ i j x, x∈A.primitives.domain i∩A.primitives.domain j →
    A.coefficient i (chartAt ℂ i x)=A.coefficient j (chartAt ℂ j x)*
      deriv ((chartAt ℂ j) ∘ (chartAt ℂ i).symm) (chartAt ℂ i x)

/-- Local primitives of one holomorphic differential differ by a
constant near any point of overlap, including its zeros. -/
theorem primitive_overlap_germ (A : HolomorphicCoefficientDisks M) (compat : A.compatibleOneForm)
    {i j x : M} (hx : x∈A.primitives.domain i∩A.primitives.domain j) :
    ∀ᶠ y in 𝓝 x, A.localIntegral i (chartAt ℂ i y)-A.localIntegral j (chartAt ℂ j y)=
      A.localIntegral i (chartAt ℂ i x)-A.localIntegral j (chartAt ℂ j x) := by
  let e := chartAt ℂ i
  let d := chartAt ℂ j
  let W := A.primitives.domain i∩A.primitives.domain j
  let S := e.target∩e.symm ⁻¹' W
  have op : IsOpen S := e.symm.isOpen_inter_preimage ((A.primitives.domain_isOpen i).inter (A.primitives.domain_isOpen j))
  have xs : e x∈S := ⟨e.map_source hx.1.1,by change e.symm (e x)∈W; rw [e.left_inv hx.1.1]; exact hx⟩
  obtain ⟨r,rp,sub⟩ := Metric.mem_nhds_iff.mp (op.mem_nhds xs)
  let f := fun z => A.localIntegral i z-A.localIntegral j (d (e.symm z))
  have diff (z : ℂ) (hz : z∈ball (e x) r) : HasDerivAt f 0 z := by
    obtain ⟨zt,xi,xj⟩ := sub hz
    have ei := e.right_inv zt
    have hi := IsManifold.subset_maximalAtlas (I := 𝓘(ℂ,ℂ)) (n := ω) (chart_mem_atlas ℂ i)
    have hj := IsManifold.subset_maximalAtlas (I := 𝓘(ℂ,ℂ)) (n := ω) (chart_mem_atlas ℂ j)
    have ht : ContDiffAt ℂ ω (d ∘ e.symm) z := contMDiffAt_iff_contDiffAt.mp
      ((contMDiffAt_of_mem_maximalAtlas hj xj.1).comp z (contMDiffAt_symm_of_mem_maximalAtlas hi zt))
    have first := A.localIntegral_hasDerivAt i (show z∈ball (e i) (A.radius i) from ei ▸ xi.2)
    have second := (A.localIntegral_hasDerivAt j xj.2).comp z (ht.differentiableAt (by simp)).hasDerivAt
    have eq := compat i j (e.symm z) ⟨xi,xj⟩
    change A.coefficient i (e (e.symm z))=A.coefficient j (d (e.symm z))*deriv (d ∘ e.symm) (e (e.symm z)) at eq
    rw [ei] at eq
    have D : HasDerivAt f (A.coefficient i z-A.coefficient j (d (e.symm z))*deriv (d ∘ e.symm) z) z := first.sub second
    rwa [eq,sub_self] at D
  have constant (z : ℂ) (hz : z∈ball (e x) r) : f z=f (e x) :=
    isOpen_ball.is_const_of_deriv_eq_zero (convex_ball _ _).isPreconnected
      (fun w hw => (diff w hw).differentiableAt.differentiableWithinAt) (fun _ hw => (diff _ hw).deriv) hz (mem_ball_self rp)
  filter_upwards [e.open_source.mem_nhds hx.1.1,(e.continuousAt hx.1.1).eventually (ball_mem_nhds _ rp)] with y hy hball
  have eq := constant (e y) hball
  simpa only [f,e.left_inv hy,e.left_inv hx.1.1] using eq

private theorem primitive_translation_chart (A : HolomorphicCoefficientDisks M) (i : M)
    (nz : A.coefficient i (chartAt ℂ i i)≠0) :
    ∃ e : OpenPartialHomeomorph M ℂ, e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M ∧ i∈e.source ∧
      e.source⊆A.primitives.domain i ∧ ∀ y : M, e y=A.localIntegral i (chartAt ℂ i y) := by
  let a := chartAt ℂ i
  let g := A.localIntegral i
  let x := a i
  have hx : x∈ball x (A.radius i) := mem_ball_self (A.radius_pos i)
  have an := A.localIntegral_analyticAt i hx
  have dn : deriv g x≠0 := (A.localIntegral_hasDerivAt i hx).deriv.trans_ne nz
  let h := an.hasStrictDerivAt
  let T : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ dn)
  have hd : HasStrictFDerivAt g T.toContinuousLinearMap x := h
  let R := hd.toOpenPartialHomeomorph g
  have mx : x∈R.source := hd.mem_toOpenPartialHomeomorph_source
  have inv : AnalyticAt ℂ R.symm (g x) := an.analyticAt_localInverse dn
  let V := {w | AnalyticAt ℂ R.symm w}
  have vo : IsOpen V := isOpen_iff_mem_nhds.mpr (fun _ h => h.eventually_analyticAt)
  let U := ball x (A.radius i) ∩ (R.source ∩ R ⁻¹' V)
  have uo : IsOpen U := isOpen_ball.inter (R.isOpen_inter_preimage vo)
  have xu : x∈U := ⟨hx,mx,inv⟩
  let e := a.trans (R.restr U)
  have source {y : M} (hy : y∈e.source) : y∈A.primitives.domain i := ⟨hy.1,(interior_subset hy.2.2).1⟩
  have xi : a.symm.symm i∈interior U := by
    rw [OpenPartialHomeomorph.symm_symm,uo.interior_eq]
    exact xu
  refine ⟨e,?_,⟨mem_chart_source ℂ i,mx,xi⟩,fun _ => source,fun _ => rfl⟩
  apply e.mem_maximalAtlas_of_contMDiffOn
  · intro y hy
    have ag : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω g (a y) :=
      contMDiffAt_iff_contDiffAt.mpr (A.localIntegral_analyticAt i (source hy).2).contDiffAt
    exact (ag.comp y (contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ i)) hy.1)).contMDiffWithinAt
  · intro w hw
    have q : R.symm w∈U := interior_subset hw.1.2
    have ai : AnalyticAt ℂ R.symm w := (R.right_inv hw.1.1) ▸ q.2.2
    have ag := (contMDiffAt_iff_contDiffAt.mpr ai.contDiffAt : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω R.symm w)
    exact ((contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ i)) hw.2).comp w ag).contMDiffWithinAt

/-- A single nonvanishing holomorphic differential suffices for
uniformization of a compact topological torus. Its local primitives,
translation atlas, global developing map and period lattice are all
derived from its actual chart coefficients. -/
theorem uniformization_of_nonvanishing_one_form [T2Space M] [CompactSpace M] {L : PeriodPair}
    (mark : M ≃ₜ PeriodTorus L) (A : HolomorphicCoefficientDisks M) (compat : A.compatibleOneForm)
    (nz : ∀ p : M, A.coefficient p (chartAt ℂ p p)≠0) :
    AdmitsPeriodTorusUniformization M := by
  choose e member center source value using fun i => A.primitive_translation_chart i (nz i)
  apply compact_torus_uniformization_of_translation_coordinates mark
  refine ⟨e,member,center,?_⟩
  intro i j x hx
  simpa only [value] using A.primitive_overlap_germ compat ⟨source i hx.1,source j hx.2⟩

end HolomorphicCoefficientDisks
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HolomorphicCoefficientDisks.uniformization_of_nonvanishing_one_form
