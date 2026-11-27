import TwoAxisHelicoid.SmoothPlaneCap

namespace TwoAxisHelicoid
open Real Set
set_option maxHeartbeats 1000000

def planeCapNorth (H : ℝ) : HelicoidTubeCoordinates := ((0,H),0)

def planeCapSphere (H : ℝ) : Set HelicoidTubeCoordinates :=
  {y | y.1.1^2+(y.1.2-H/2)^2+y.2^2 = (H/2)^2}

noncomputable def stereographicPlaneCap (H : ℝ) (p : ℝ × ℝ) : HelicoidTubeCoordinates :=
  let q := p.1^2+p.2^2
  ((H/(1+q)*p.1,H*(q/(1+q))),H/(1+q)*p.2)

theorem smoothPlaneCap_eq_stereographic {A H : ℝ} {p : ℝ × ℝ}
    (hp : A+1 ≤ p.1^2+p.2^2) : smoothPlaneCap A H p = stereographicPlaneCap H p := by
  simp [smoothPlaneCap,stereographicPlaneCap,planeCapScale,planeCapHeight,planeCapSwitch_one hp]

theorem stereographicPlaneCap_mem_sphere (H : ℝ) (p : ℝ × ℝ) :
    stereographicPlaneCap H p ∈ planeCapSphere H := by
  have hd : 1+(p.1^2+p.2^2) ≠ 0 := by positivity
  dsimp [stereographicPlaneCap,planeCapSphere]
  field_simp
  ring

theorem planeCapNorth_mem_sphere (H : ℝ) : planeCapNorth H ∈ planeCapSphere H := by
  dsimp [planeCapNorth,planeCapSphere]
  ring

theorem sphere_cap_height_bounds {H : ℝ} (hH : 0 < H) {y : HelicoidTubeCoordinates}
    (hy : y ∈ planeCapSphere H) : 0 ≤ y.1.2 ∧ y.1.2 ≤ H := by
  change y.1.1^2+(y.1.2-H/2)^2+y.2^2 = (H/2)^2 at hy
  constructor <;> nlinarith [sq_nonneg y.1.1,sq_nonneg y.2]

theorem sphere_cap_height_lt {H : ℝ} (hH : 0 < H) {y : HelicoidTubeCoordinates}
    (hy : y ∈ planeCapSphere H) (hn : y ≠ planeCapNorth H) : y.1.2 < H := by
  apply lt_of_le_of_ne (sphere_cap_height_bounds hH hy).2
  intro he
  have hx : y.1.1 = 0 := by
    change y.1.1^2+(y.1.2-H/2)^2+y.2^2 = (H/2)^2 at hy
    nlinarith [sq_nonneg y.2,sq_nonneg y.1.1]
  have hz : y.2 = 0 := by
    change y.1.1^2+(y.1.2-H/2)^2+y.2^2 = (H/2)^2 at hy
    nlinarith [sq_nonneg y.1.1,sq_nonneg y.2]
  exact hn (Prod.ext (Prod.ext hx he) hz)

theorem stereographicPlaneCap_inverse {H : ℝ} (hH : 0 < H) {y : HelicoidTubeCoordinates}
    (hy : y ∈ planeCapSphere H) (hn : y ≠ planeCapNorth H) :
    stereographicPlaneCap H (y.1.1/(H-y.1.2),y.2/(H-y.1.2)) = y := by
  have hd : H-y.1.2 ≠ 0 := (sub_pos.mpr (sphere_cap_height_lt hH hy hn)).ne'
  have hs : y.1.1^2+y.2^2 = y.1.2*(H-y.1.2) := by
    change y.1.1^2+(y.1.2-H/2)^2+y.2^2 = (H/2)^2 at hy
    nlinarith
  have hq : (y.1.1/(H-y.1.2))^2+(y.2/(H-y.1.2))^2 = y.1.2/(H-y.1.2) := by
    field_simp
    nlinarith [hs]
  have hden : 1+y.1.2/(H-y.1.2) = H/(H-y.1.2) := by
    field_simp
    ring
  dsimp [stereographicPlaneCap]
  rw [hq,hden]
  apply Prod.ext
  · apply Prod.ext <;> field_simp
  · field_simp

theorem planeCapHeight_le_rational {A H q : ℝ} (hH : 0 ≤ H) (hq : 0 ≤ q) :
    planeCapHeight A H q ≤ H*(q/(1+q)) := by
  apply mul_le_mul_of_nonneg_left _ hH
  exact mul_le_of_le_one_left (by positivity) (planeCapSwitch_le_one A q)

theorem cap_rational_height_mono {H q r : ℝ} (hH : 0 ≤ H) (hq : 0 ≤ q) (hqr : q ≤ r) :
    H*(q/(1+q)) ≤ H*(r/(1+r)) := by
  apply mul_le_mul_of_nonneg_left _ hH
  apply (div_le_div_iff₀ (by linarith : 0 < 1+q) (by linarith : 0 < 1+r)).mpr
  nlinarith

/-- A full ambient neighborhood of the added point is exactly a round
sphere. Thus no geometric regularity at the added point is postulated. -/
theorem smoothPlaneCap_spherical_neighborhood {A H : ℝ} (hA : 0 ≤ A) (hH : 0 < H) :
    ∃ U : Set HelicoidTubeCoordinates, IsOpen U ∧ planeCapNorth H ∈ U ∧
      insert (planeCapNorth H) (range (smoothPlaneCap A H)) ∩ U = planeCapSphere H ∩ U := by
  let B := A+1
  let threshold := H*(B/(1+B))
  let U : Set HelicoidTubeCoordinates := {y | threshold < y.1.2}
  have hB : 0 < B := by dsimp [B]; linarith
  have hthreshold : threshold < H := by
    have hh : B/(1+B) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    simpa [threshold] using mul_lt_mul_of_pos_left hh hH
  refine ⟨U,isOpen_lt continuous_const (by fun_prop),hthreshold,?_⟩
  ext y
  constructor
  · rintro ⟨hy,hU⟩
    refine ⟨?_,hU⟩
    rcases hy with rfl | ⟨p,rfl⟩
    · exact planeCapNorth_mem_sphere H
    · have hq : B < p.1^2+p.2^2 := by
        by_contra hn
        have hle := (planeCapHeight_le_rational (A := A) hH.le
          (add_nonneg (sq_nonneg p.1) (sq_nonneg p.2))).trans
          (cap_rational_height_mono hH.le (by positivity) (le_of_not_gt hn))
        exact (show threshold < planeCapHeight A H (p.1^2+p.2^2) from hU).not_ge hle
      rw [smoothPlaneCap_eq_stereographic hq.le]
      exact stereographicPlaneCap_mem_sphere H p
  · rintro ⟨hy,hU⟩
    refine ⟨?_,hU⟩
    by_cases hn : y = planeCapNorth H
    · exact Or.inl hn
    · let p : ℝ × ℝ := (y.1.1/(H-y.1.2),y.2/(H-y.1.2))
      have he : stereographicPlaneCap H p = y := stereographicPlaneCap_inverse hH hy hn
      have hq : B < p.1^2+p.2^2 := by
        by_contra hnq
        have hle := cap_rational_height_mono hH.le
          (add_nonneg (sq_nonneg p.1) (sq_nonneg p.2)) (le_of_not_gt hnq)
        have hh := congrArg (fun z : HelicoidTubeCoordinates => z.1.2) he
        change H*((p.1^2+p.2^2)/(1+(p.1^2+p.2^2))) = y.1.2 at hh
        rw [hh] at hle
        exact (show threshold < y.1.2 from hU).not_ge hle
      exact Or.inr ⟨p,(smoothPlaneCap_eq_stereographic hq.le).trans he⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.smoothPlaneCap_spherical_neighborhood
