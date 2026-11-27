import TwoAxisHelicoid.ComplexCurvePunctureCutoff
import TwoAxisHelicoid.SingleChartSurfaceStokes
import TwoAxisHelicoid.SquareChartGreen
import TwoAxisHelicoid.SquarePunctureResidue

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory Metric Topology Function
open scoped Topology Manifold ContDiff Interval

/-- A global complex one-form on a compact Riemann surface, holomorphic
except at one point, has zero residue there. The isolated singularity
may be essential. All cutoff, compact support and boundary integrals
refer to the specified chart of the same surface. -/
theorem compact_curve_single_puncture_residue_zero {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    {P : M} (a : OpenPartialHomeomorph M ℂ → ℂ → ℂ)
    (hol : ∀ e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M, ∀ z∈e.target, e.symm z≠P → AnalyticAt ℂ (a e) z)
    (law : ∀ e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M, ∀ d∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M,
      ∀ z∈(e.symm.trans d).source, e.symm z≠P →
        a e z=a d ((e.symm.trans d) z)*deriv (e.symm.trans d) z)
    {d : OpenPartialHomeomorph M ℂ} (hd : d∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
    (hp : P∈d.source) (center : d P=0) {c : ℂ} (res : HasPunctureResidue (a d) c) : c=0 := by
  classical
  have target : (0:ℂ)∈d.target := center ▸ d.map_source hp
  have inv : d.symm 0=P := by rw [← center,d.left_inv hp]
  have punct (z : ℂ) (hz : z∈d.target) (nz : z≠0) : d.symm z≠P := by
    intro h
    exact nz ((d.right_inv hz).symm.trans ((congrArg d h).trans center))
  have germ : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ (a d) z := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (d.open_target.mem_nhds target)] with z nz hz
    exact (hol d hd z hz (punct z hz nz)).differentiableAt
  obtain ⟨D,Dp,square⟩ := res.small_square_integrals germ
  obtain ⟨S,Sp,ballS⟩ := Metric.mem_nhds_iff.mp (d.open_target.mem_nhds target)
  let r := min D S/4
  have rp : 0<r := div_pos (lt_min Dp Sp) (by norm_num)
  have rd : r<D := by dsimp [r]; linarith [min_le_left D S,lt_min Dp Sp]
  have rs : 2*r<S := by dsimp [r]; linarith [min_le_right D S,lt_min Dp Sp]
  let K := Icc (-r) r ×ℂ Icc (-r) r
  have compact : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have sub (z : ℂ) (hz : z∈K) : z∈d.target := by
    apply ballS
    apply mem_ball_zero_iff.mpr
    have n := Complex.norm_le_abs_re_add_abs_im z
    have b1 := abs_le.mpr hz.1
    have b2 := abs_le.mpr hz.2
    linarith
  let B := closedBall (0:ℂ) (r/2)
  have bs (z : ℂ) (hz : z∈B) : z∈K := by
    have n := mem_closedBall_zero_iff.mp hz
    exact ⟨abs_le.mp ((Complex.abs_re_le_norm z).trans (by linarith)),
      abs_le.mp ((Complex.abs_im_le_norm z).trans (by linarith))⟩
  obtain ⟨ρ,one,zero,smooth⟩ := complex_curve_puncture_cutoff hd hp center (half_pos rp) (fun z hz => sub z (bs z hz))
  let A := fun (e : OpenPartialHomeomorph M ℂ) w => (1-(ρ (e.symm w):ℂ))*a e w
  have eqOne (e : OpenPartialHomeomorph M ℂ) {z : ℂ} (hz : z∈e.target) (hit : e.symm z=P) :
      A e =ᶠ[𝓝 z] 0 := by
    have cv : Tendsto e.symm (𝓝 z) (𝓝 P) := hit ▸ e.continuousAt_symm hz
    filter_upwards [one.comp_tendsto cv] with w hw
    change ρ (e.symm w)=1 at hw
    simp only [A,hw,Complex.ofReal_one,sub_self,zero_mul,Pi.zero_apply]
  have eqOff (e : OpenPartialHomeomorph M ℂ) {z : ℂ} (hz : z∈e.target)
      (out : e.symm z∉d.symm '' B) : A e =ᶠ[𝓝 z] a e := by
    filter_upwards [(zero _ out).comp_tendsto (e.continuousAt_symm hz)] with w hw
    change ρ (e.symm w)=0 at hw
    simp only [A,hw,Complex.ofReal_zero,sub_zero,one_mul]
  have reg (e : OpenPartialHomeomorph M ℂ) (he : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
      (z : ℂ) (hz : z∈e.target) : ContDiffAt ℝ 1 (A e) z := by
    by_cases hit : e.symm z=P
    · exact (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq (eqOne e hz hit)
    · have k := Complex.ofRealCLM.contDiff.contDiffAt.comp z (smooth e he z hz)
      exact (contDiffAt_const.sub k).mul (((hol e he z hz hit).contDiffAt).restrict_scalars ℝ)
  have compat (e : OpenPartialHomeomorph M ℂ) (he : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
      (q : OpenPartialHomeomorph M ℂ) (hq : q∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
      (z : ℂ) (hz : z∈(e.symm.trans q).source) :
      A e z=A q ((e.symm.trans q) z)*deriv (e.symm.trans q) z := by
    have same : q.symm ((e.symm.trans q) z)=e.symm z := q.left_inv hz.2
    by_cases hit : e.symm z=P
    · rw [(eqOne e hz.1 hit).self_of_nhds,
        (eqOne q (z:=(e.symm.trans q) z) (q.map_source hz.2) (same.trans hit)).self_of_nhds]
      simp
    · simp only [A,same,law e he q hq z hz hit,mul_assoc]
  have away (e : OpenPartialHomeomorph M ℂ) (he : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
      (z : ℂ) (hz : z∈e.target) (out : e.symm z∉d.symm '' B) :
      complexFormExteriorCoefficient (A e) z=0 := by
    have cp : P∈d.symm '' B := ⟨0,mem_closedBall_self (by positivity),inv⟩
    have nz : e.symm z≠P := fun h => out (h ▸ cp)
    simp only [complexFormExteriorCoefficient,(eqOff e hz out).fderiv_eq]
    exact complex_form_exterior_of_holomorphic (hol e he z hz nz).differentiableAt
  have dout {z : ℂ} (hz : z∈d.target) (out : z∉B) : d.symm z∉d.symm '' B := by
    rintro ⟨v,hv,eq⟩
    exact out ((d.symm.injOn (sub v (bs v hv)) hz eq) ▸ hv)
  have supp (z : ℂ) (hz : z∈d.target) (out : z∉K) : complexFormExteriorCoefficient (A d) z=0 :=
    away d hd z hz (dout hz (fun h => out (bs z h)))
  have stokes := compact_curve_stokes_in_chart A reg compat d hd (fun i z hz outside =>
    away _ (IsManifold.chart_mem_maximalAtlas _) z hz (fun ⟨v,hv,eq⟩ => outside (eq ▸ d.map_target (sub v (bs v hv))))) compact sub supp
  have area : (∫ z in K, complexFormExteriorCoefficient (A d) z)=0 := by
    rw [← setIntegral_eq_of_subset_of_forall_sdiff_eq_zero d.open_target.measurableSet sub (fun z hz => supp z hz.1 hz.2)]
    exact stokes
  have boundary : rectangleBoundary (A d) r r=0 := (square_boundary_eq_exterior_area rp.le (fun z hz => reg d hd z (sub z hz))).trans area
  have edge (z : ℂ) (hz : z∈K) (h : |z.re|=r ∨ |z.im|=r) : A d z=a d z := by
    apply (eqOff d (sub z hz) (dout (sub z hz) ?_)).self_of_nhds
    intro inside
    have upper := mem_closedBall_zero_iff.mp inside
    rcases h with h|h
    · linarith [Complex.abs_re_le_norm z]
    · linarith [Complex.abs_im_le_norm z]
  have directly : rectangleBoundary (A d) r r=rectangleBoundary (a d) r r := by
    have ord : -r≤r := by linarith
    apply rectangleBoundary_congr <;> intro t ht <;> rw [uIcc_of_le ord] at ht <;>
      apply edge <;> simp [K,mem_reProdIm,abs_of_pos rp,ht.1,ht.2,ord]
  have total := (square r ⟨rp,rd⟩).symm.trans (directly.symm.trans boundary)
  exact (mul_eq_zero.mp total).resolve_right (by exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_curve_single_puncture_residue_zero
