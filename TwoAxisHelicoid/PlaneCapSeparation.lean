import TwoAxisHelicoid.SmoothPlaneCap

namespace TwoAxisHelicoid
open Real Set
set_option maxHeartbeats 1000000

/-- The turned-back cap stays strictly outside the prescribed core ball.
The estimate is in the actual Euclidean squared radius. -/
theorem smoothPlaneCap_outside_core {A H R : ℝ} (hR : 0 < R) (hH : 4*R ≤ H)
    {p : ℝ × ℝ} (hp1 : 1 ≤ p.1^2+p.2^2) (hpR : 4*R^2 ≤ p.1^2+p.2^2) :
    R^2 < ambientRadiusSq (smoothPlaneCap A H p) := by
  let q := p.1^2+p.2^2
  let c := planeCapSwitch A q
  let radial := planeCapScale A H q*sqrt q
  let height := planeCapHeight A H q
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hden : 0 < 1+q := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hc0 : 0 ≤ c := planeCapSwitch_nonneg A q
  have hc1 : c ≤ 1 := planeCapSwitch_le_one A q
  have hs : 2*R ≤ sqrt q := by
    have hh := sq_sqrt hq0
    have hn := sqrt_nonneg q
    change 4*R^2 ≤ q at hpR
    nlinarith
  have hf : 1/2 ≤ q/(1+q) := by
    apply (le_div_iff₀ hden).mpr
    change 1 ≤ q at hp1
    linarith
  have hb : 2*R ≤ H/(1+q)*sqrt q+H*(q/(1+q)) := by
    have hm := mul_le_mul_of_nonneg_left hf hH0
    have hn : 0 ≤ H/(1+q)*sqrt q := by positivity
    linarith
  have he : radial+height = (1-c)*sqrt q+c*(H/(1+q)*sqrt q+H*(q/(1+q))) := by
    dsimp [radial,height,planeCapScale,planeCapHeight,c]
    ring
  have hsum : 2*R ≤ radial+height := by
    rw [he]
    have h1 := mul_nonneg (sub_nonneg.mpr hc1) (sub_nonneg.mpr hs)
    have h2 := mul_nonneg hc0 (sub_nonneg.mpr hb)
    nlinarith
  have hradius : ambientRadiusSq (smoothPlaneCap A H p) = radial^2+height^2 := by
    dsimp [ambientRadiusSq,smoothPlaneCap,radial,height,q]
    rw [mul_pow,mul_pow,mul_pow,sq_sqrt (add_nonneg (sq_nonneg p.1) (sq_nonneg p.2))]
    ring
  rw [hradius]
  have hsquare : (2*R)^2 ≤ (radial+height)^2 :=
    (sq_le_sq₀ (by positivity) (by linarith)).mpr hsum
  nlinarith [sq_nonneg (radial-height),sq_pos_of_pos hR]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.smoothPlaneCap_outside_core
