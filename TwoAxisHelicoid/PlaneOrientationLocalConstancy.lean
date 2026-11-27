import TwoAxisHelicoid.PlaneOrientationGermComposition
import Mathlib.Algebra.Group.Int.Units

namespace TwoAxisHelicoid
open Complex Filter Set Topology Metric
open scoped Topology

/-- The link of a local plane homeomorphism has degree one or minus one.
Composing with its true local inverse yields degree one. -/
theorem openPartialHomeomorph_orientation_sign (e : OpenPartialHomeomorph ℂ ℂ) {p : ℂ}
    (hp : p ∈ e.source) : ∃ n : ℤ, (n = 1 ∨ n = -1) ∧ HasPlaneOrientationAt e p n := by
  obtain ⟨n,hn⟩ := openPartialHomeomorph_plane_orientation_exists e hp
  obtain ⟨m,hm⟩ := openPartialHomeomorph_plane_orientation_exists e.symm (e.map_source hp)
  have hc := openPartialHomeomorph_plane_orientation_comp e e.symm hp (e.map_source hp) hm hn
  have he : id =ᶠ[𝓝 p] e.symm ∘ e := by
    filter_upwards [e.open_source.mem_nhds hp] with z hz
    exact (e.left_inv hz).symm
  have hu : m*n = 1 := (hc.congr he).unique (planeOrientation_identity p)
  exact ⟨n,((Int.mul_eq_one_iff_eq_one_or_neg_one.mp hu).imp And.right And.right),hn⟩

/-- The local signed degree cannot change as the center moves inside a
plane homeomorphism chart. Both the moving centers and the moving link
stay in one injective disk. -/
theorem openPartialHomeomorph_orientation_locally_constant (e : OpenPartialHomeomorph ℂ ℂ) {p : ℂ}
    (hp : p ∈ e.source) {n : ℤ} (hn : HasPlaneOrientationAt e p n) :
    ∀ᶠ q in 𝓝 p, HasPlaneOrientationAt e q n := by
  obtain ⟨B,hB,hU⟩ := Metric.mem_nhds_iff.mp (e.open_source.mem_nhds hp)
  obtain ⟨R,hR,hr⟩ := hn
  let b := B/3
  have hb : 0 < b := by dsimp [b]; positivity
  have hbig : 2*b < B := by dsimp [b]; linarith
  filter_upwards [ball_mem_nhds p hb] with q hq
  have hqp : ‖q-p‖ < b := by simpa only [mem_ball,dist_eq_norm] using hq
  have hqs : q ∈ e.source := hU (show dist q p < B from (show dist q p < b from hq).trans (by linarith))
  obtain ⟨m,hm⟩ := openPartialHomeomorph_plane_orientation_exists e hqs
  obtain ⟨S,hS,hs⟩ := hm
  let r := min (min R S) b/2
  have hmin : 0 < min (min R S) b := lt_min (lt_min hR hS) hb
  have hrp : 0 < r := half_pos hmin
  have hlt : r < min (min R S) b := half_lt_self hmin
  have hrR := hlt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hrS := hlt.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hrb := hlt.trans_le (min_le_right _ _)
  let c := fun t : ℝ => p+orientationBlend t • (q-p)
  have hcb (t : ℝ) : dist (c t) p < b := by
    rw [dist_eq_norm,show c t-p = orientationBlend t • (q-p) by dsimp [c]; abel,norm_smul,
      Real.norm_of_nonneg (orientationBlend_mem t).1]
    exact ((mul_le_mul_of_nonneg_right (orientationBlend_mem t).2 (norm_nonneg (q-p))).trans_eq (one_mul _)).trans_lt hqp
  have hcs (t : ℝ) : c t ∈ e.source := hU ((hcb t).trans (by linarith))
  have hcs' (x : ℝ × OrientationCircle) : c x.1+r • orientationRay x.2 ∈ e.source := by
    apply hU
    have h' := dist_triangle (c x.1+r • orientationRay x.2) (c x.1) p
    have hdist : dist (c x.1+r • orientationRay x.2) (c x.1) = r := by
      rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hrp.le,orientationRay_norm,mul_one]
    rw [hdist] at h'
    exact h'.trans_lt (by linarith [hcb x.1])
  let K := fun x : ℝ × OrientationCircle => planeOrientationProbe e (c x.1) r x.2
  have hcont : Continuous c := continuous_const.add (orientationBlend_continuous.smul continuous_const)
  have hK : Continuous K := continuous_planeOrientationProbe_family e.continuousOn e.injOn
    (hcont.comp continuous_fst) continuous_const continuous_snd (fun _ => hrp) (fun x => hcs x.1) hcs'
  have hzero : HasOrientationCircleDegree (fun a => K (0,a)) n := by simpa [K,c] using hr r ⟨hrp,hrR⟩
  have hone : HasOrientationCircleDegree (fun a => K (1,a)) m := by simpa [K,c] using hs r ⟨hrp,hrS⟩
  have he := (hzero.family (t := 1) hK).unique hone
  exact he.symm ▸ ⟨S,hS,hs⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.openPartialHomeomorph_orientation_locally_constant
