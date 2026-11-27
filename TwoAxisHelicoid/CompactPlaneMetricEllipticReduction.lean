import TwoAxisHelicoid.ScalarHarmonicMetricUniformization
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology
open scoped ContDiff

/-- The scalar PDE for a smooth determinant-one metric on the whole plane
which equals the Euclidean metric outside a compact set. -/
def CompactUnitMetricScalarExists : Prop :=
  ∀ A B C : ℂ → ℝ, ContDiff ℝ ∞ A → ContDiff ℝ ∞ B → ContDiff ℝ ∞ C →
    (∀ z, 0<A z) → (∀ z, A z*C z-(B z)^2=1) →
    (∃ K : Set ℂ, IsCompact K ∧ ∀ z∉K, A z=1 ∧ B z=0 ∧ C z=1) →
    ∀ p : ℂ, ∃ (r : ℝ) (u : ℂ → ℝ), 0<r ∧ fderiv ℝ u p 1=1 ∧
      ∀ z∈ball p r, ContDiffAt ℝ ∞ u z ∧
        fderiv ℝ (fun y => C y*fderiv ℝ u y 1-B y*fderiv ℝ u y I) z 1 =
        fderiv ℝ (fun y => B y*fderiv ℝ u y 1-A y*fderiv ℝ u y I) z I

/-- In two dimensions the metric can be normalized by its area density,
then extended smoothly as the identity without changing the PDE near the
chosen point. Both reductions preserve the prescribed first derivative. -/
theorem scalar_elliptic_existence_iff_compact_unit_metric :
    LocalMetricHarmonicScalarExists ↔ CompactUnitMetricScalarExists := by
  constructor
  · intro solve A B C sa sb sc ha det _ p
    have metric (z : ℂ) (_ : z∈(univ : Set ℂ)) :
        ContDiffAt ℝ ∞ A z ∧ ContDiffAt ℝ ∞ B z ∧ ContDiffAt ℝ ∞ C z ∧
          0<A z ∧ (B z)^2<A z*C z :=
      ⟨sa.contDiffAt,sb.contDiffAt,sc.contDiffAt,ha z,by linarith [det z]⟩
    obtain ⟨r,u,rp,_,first,regular⟩ := solve univ isOpen_univ A B C metric p (mem_univ p)
    refine ⟨r,u,rp,first,fun z hz => ⟨(regular z hz).1,?_⟩⟩
    have xs : metricConjugateSecond A B C u =
        (fun y => C y*fderiv ℝ u y 1-B y*fderiv ℝ u y I) := by
      funext y
      simp only [metricConjugateSecond,planeMetricArea,det,Real.sqrt_one,div_one]
    have ys : metricConjugateFirst A B C u =
        (fun y => B y*fderiv ℝ u y 1-A y*fderiv ℝ u y I) := by
      funext y
      simp only [metricConjugateFirst,planeMetricArea,det,Real.sqrt_one,div_one]
    simpa only [xs,ys] using (regular z hz).2
  · intro solve U op E F G smooth p hp
    obtain ⟨d,dp,inside⟩ := Metric.mem_nhds_iff.mp (op.mem_nhds hp)
    let bump : ContDiffBump p := ⟨d/4,d/2,by positivity,by linarith⟩
    let K := closedBall p (d/2)
    let W := planeMetricArea E F G
    let A := fun z => 1 + bump z*(E z/W z-1)
    let B := fun z => bump z*(F z/W z)
    let C := fun z => (1+(B z)^2)/A z
    have ku {z : ℂ} (hz : z∈K) : z∈U :=
      inside (show dist z p<d from lt_of_le_of_lt hz (by linarith))
    have area {z : ℂ} (hz : z∈U) : 0<W z :=
      Real.sqrt_pos.mpr (sub_pos.mpr (smooth z hz).2.2.2.2)
    have sw {z : ℂ} (hz : z∈U) : ContDiffAt ℝ ∞ W z := by
      obtain ⟨se,sf,sg,_,det⟩ := smooth z hz
      exact ((se.mul sg).sub (sf.pow 2)).sqrt (sub_pos.mpr det).ne'
    have off {z : ℂ} (hz : z∉K) : bump z=0 :=
      bump.zero_of_le_dist (not_le.mp hz).le
    have outside {z : ℂ} (hz : z∉K) :
        (A =ᶠ[𝓝 z] (fun _ => 1)) ∧ (B =ᶠ[𝓝 z] (fun _ => 0)) := by
      have near : ∀ᶠ y in 𝓝 z, y∉K := isClosed_closedBall.isOpen_compl.mem_nhds hz
      constructor
      · filter_upwards [near] with y hy using (by simp [A,off hy])
      · filter_upwards [near] with y hy using (by simp [B,off hy])
    have sa : ContDiff ℝ ∞ A := contDiff_iff_contDiffAt.mpr fun z => by
      by_cases h : z∈K
      · exact contDiffAt_const.add (bump.contDiffAt.mul
          (((smooth z (ku h)).1.div (sw (ku h)) (area (ku h)).ne').sub contDiffAt_const))
      · exact contDiffAt_const.congr_of_eventuallyEq (outside h).1
    have sb : ContDiff ℝ ∞ B := contDiff_iff_contDiffAt.mpr fun z => by
      by_cases h : z∈K
      · exact bump.contDiffAt.mul ((smooth z (ku h)).2.1.div (sw (ku h)) (area (ku h)).ne')
      · exact contDiffAt_const.congr_of_eventuallyEq (outside h).2
    have positive (z : ℂ) : 0<A z := by
      by_cases h : z∈K
      · have t : 0<E z/W z := div_pos (smooth z (ku h)).2.2.2.1 (area (ku h))
        by_cases zero : bump z=0
        · simp [A,zero]
        · have product := mul_pos (lt_of_le_of_ne bump.nonneg (Ne.symm zero)) t
          dsimp [A]
          nlinarith [show bump z≤1 from bump.le_one]
      · simp [A,off h]
    have sc : ContDiff ℝ ∞ C :=
      (contDiff_const.add (sb.pow 2)).div sa (fun z => (positive z).ne')
    have det (z : ℂ) : A z*C z-(B z)^2=1 := by
      dsimp [C]
      field_simp [(positive z).ne']
      ring
    have euclidean : ∀ z∉K, A z=1 ∧ B z=0 ∧ C z=1 := by
      intro z hz
      simp [A,B,C,off hz]
    obtain ⟨r,u,rp,first,harm⟩ :=
      solve A B C sa sb sc positive det ⟨K,isCompact_closedBall _ _,euclidean⟩ p
    let s := min r bump.rIn
    have sr : s≤r := min_le_left _ _
    have si : s≤bump.rIn := min_le_right _ _
    have inner {z : ℂ} (hz : z∈ball p s) : z∈ball p bump.rIn := ball_subset_ball si hz
    have inK {z : ℂ} (hz : z∈ball p bump.rIn) : z∈K :=
      ball_subset_closedBall (ball_subset_ball bump.rIn_lt_rOut.le hz)
    have agrees {z : ℂ} (hz : z∈ball p bump.rIn) :
        A z=E z/W z ∧ B z=F z/W z ∧ C z=G z/W z := by
      have bu := bump.one_of_mem_closedBall (ball_subset_closedBall hz)
      have ap : A z=E z/W z := by simp [A,bu]
      have bp : B z=F z/W z := by simp [B,bu]
      have he := (smooth z (ku (inK hz))).2.2.2.1
      have hw := area (ku (inK hz))
      have ws : W z^2=E z*G z-(F z)^2 :=
        Real.sq_sqrt (sub_pos.mpr (smooth z (ku (inK hz))).2.2.2.2).le
      refine ⟨ap,bp,?_⟩
      change (1+(B z)^2)/A z=G z/W z
      rw [ap,bp,div_eq_iff (div_pos he hw).ne']
      field_simp [hw.ne']
      nlinarith [ws]
    refine ⟨s,u,lt_min rp bump.rIn_pos,fun z hz => ku (inK (inner hz)),first,?_⟩
    intro z hz
    obtain ⟨su,pde⟩ := harm z (ball_subset_ball sr hz)
    have near : ∀ᶠ y in 𝓝 z, y∈ball p bump.rIn := isOpen_ball.mem_nhds (inner hz)
    have xflux : metricConjugateSecond E F G u =ᶠ[𝓝 z]
        (fun y => C y*fderiv ℝ u y 1 - B y*fderiv ℝ u y I) := by
      filter_upwards [near] with y hy
      rw [(agrees hy).2.2,(agrees hy).2.1]
      dsimp [metricConjugateSecond,W]
      ring
    have yflux : metricConjugateFirst E F G u =ᶠ[𝓝 z]
        (fun y => B y*fderiv ℝ u y 1 - A y*fderiv ℝ u y I) := by
      filter_upwards [near] with y hy
      rw [(agrees hy).2.1,(agrees hy).1]
      dsimp [metricConjugateFirst,W]
      ring
    exact ⟨su,by rwa [xflux.fderiv_eq,yflux.fderiv_eq]⟩
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.scalar_elliptic_existence_iff_compact_unit_metric
