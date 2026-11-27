import TwoAxisHelicoid.PlaneOrientationRay

namespace TwoAxisHelicoid
open Complex Set Filter Topology Metric
open scoped Topology

noncomputable def planeOrientationProbe (f : ℂ → ℂ) (p : ℂ) (r : ℝ) (a : OrientationCircle) : OrientationCircle :=
  planeOrientationDirection (f (p+r • orientationRay a)-f p)

/-- The common integer degree on all sufficiently small circles is a
local property of the map at the center. -/
def HasPlaneOrientationAt (f : ℂ → ℂ) (p : ℂ) (n : ℤ) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∀ r ∈ Ioo 0 R, HasOrientationCircleDegree (planeOrientationProbe f p r) n

theorem HasPlaneOrientationAt.unique {f : ℂ → ℂ} {p : ℂ} {m n : ℤ}
    (hm : HasPlaneOrientationAt f p m) (hn : HasPlaneOrientationAt f p n) : m = n := by
  obtain ⟨R,hR,hr⟩ := hm
  obtain ⟨S,hS,hs⟩ := hn
  let r := min R S/2
  have hpos : 0 < r := half_pos (lt_min hR hS)
  have hlt : r < min R S := half_lt_self (lt_min hR hS)
  exact (hr _ ⟨hpos,hlt.trans_le (min_le_left _ _)⟩).unique (hs _ ⟨hpos,hlt.trans_le (min_le_right _ _)⟩)

noncomputable def orientationBlend (t : ℝ) := max 0 (min 1 t)

theorem orientationBlend_continuous : Continuous orientationBlend := by unfold orientationBlend; fun_prop

theorem orientationBlend_mem (t : ℝ) : orientationBlend t ∈ Icc 0 1 :=
  ⟨le_max_left _ _,max_le zero_le_one (min_le_left _ _)⟩

@[simp] theorem orientationBlend_zero : orientationBlend 0 = 0 := by norm_num [orientationBlend]
@[simp] theorem orientationBlend_one : orientationBlend 1 = 1 := by norm_num [orientationBlend]

noncomputable def orientationInterpolate (t r s : ℝ) : ℝ :=
  (1-orientationBlend t)*r+orientationBlend t*s

theorem orientationInterpolate_mem {R r s : ℝ} (hr : r ∈ Ioo 0 R) (hs : s ∈ Ioo 0 R) (t : ℝ) :
    orientationInterpolate t r s ∈ Ioo 0 R := by
  let v := orientationBlend t
  have hv := orientationBlend_mem t
  have hsum : 1-v+v = 1 := by ring
  exact (convex_Ioo (𝕜 := ℝ) 0 R) hr hs (sub_nonneg.mpr hv.2) hv.1 hsum

@[simp] theorem orientationInterpolate_zero (r s : ℝ) : orientationInterpolate 0 r s = r := by simp [orientationInterpolate]
@[simp] theorem orientationInterpolate_one (r s : ℝ) : orientationInterpolate 1 r s = s := by simp [orientationInterpolate]

/-- A continuous family of positive small circles may vary its center
and radius inside any honest injective chart. The image directions vary
continuously on the whole parameter family. -/
theorem continuous_planeOrientationProbe_family {E : Type*} [TopologicalSpace E]
    {f : ℂ → ℂ} {U : Set ℂ} (hf : ContinuousOn f U) (hinj : InjOn f U)
    {p : E → ℂ} {r : E → ℝ} {a : E → OrientationCircle}
    (hp : Continuous p) (hr : Continuous r) (ha : Continuous a) (hpos : ∀ x, 0 < r x)
    (hpU : ∀ x, p x ∈ U) (hU : ∀ x, p x+r x • orientationRay (a x) ∈ U) :
    Continuous (fun x => planeOrientationProbe f (p x) (r x) (a x)) := by
  have h₁ := hf.comp_continuous (hp.add (hr.smul (orientationRay_continuous.comp ha))) hU
  have h₂ := hf.comp_continuous hp hpU
  have hn (x : E) : f (p x+r x • orientationRay (a x))-f (p x) ≠ 0 := by
    intro he
    have h := hinj (hU x) (hpU x) (sub_eq_zero.mp he)
    exact smul_ne_zero (hpos x).ne' (orientationRay_ne_zero _) (add_eq_left.mp h)
  exact continuous_iff_continuousAt.mpr fun x =>
    (planeOrientationDirection_continuousAt (hn x)).comp (f := fun x => f (p x+r x • orientationRay (a x))-f (p x)) (h₁.sub h₂).continuousAt

theorem orientation_probe_point_mem_ball {p : ℂ} {r R : ℝ} (hr : r ∈ Ioo 0 R) (a : OrientationCircle) :
    p+r • orientationRay a ∈ ball p R := by
  simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,orientationRay_norm,mul_one,
    Real.norm_of_nonneg hr.1.le] using hr.2

/-- The signed degree of the image of a small circle is independent of its
radius as long as the enclosing disk lies in the injectivity domain. -/
theorem orientation_probe_radius_degree {f : ℂ → ℂ} {p : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ContinuousOn f (ball p R)) (hinj : InjOn f (ball p R)) :
    ∃ n : ℤ, ∀ r ∈ Ioo 0 R, HasOrientationCircleDegree (planeOrientationProbe f p r) n := by
  let d := R/2
  have hd : d ∈ Ioo 0 R := ⟨half_pos hR,half_lt_self hR⟩
  have hc : Continuous (planeOrientationProbe f p d) :=
    continuous_planeOrientationProbe_family hf hinj continuous_const continuous_const continuous_id (fun _ => hd.1)
      (fun _ => mem_ball_self hR) (fun a => orientation_probe_point_mem_ball hd a)
  obtain ⟨n,hn⟩ := orientationCircle_degree_exists hc
  refine ⟨n,fun r hr => ?_⟩
  let K := fun x : ℝ × OrientationCircle => planeOrientationProbe f p (orientationInterpolate x.1 d r) x.2
  have hK : Continuous K := by
    apply continuous_planeOrientationProbe_family hf hinj continuous_const _ continuous_snd
      (fun x => (orientationInterpolate_mem hd hr x.1).1) (fun _ => mem_ball_self hR)
      (fun x => orientation_probe_point_mem_ball (orientationInterpolate_mem hd hr x.1) x.2)
    exact (((continuous_const.sub (orientationBlend_continuous.comp continuous_fst)).mul continuous_const).add
      ((orientationBlend_continuous.comp continuous_fst).mul continuous_const))
  have hzero : HasOrientationCircleDegree (fun a => K (0,a)) n := by simpa only [K,orientationInterpolate_zero] using hn
  simpa only [K,orientationInterpolate_one] using hzero.family (t := 1) hK

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.orientation_probe_radius_degree
