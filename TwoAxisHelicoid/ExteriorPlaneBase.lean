import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Bounded

namespace TwoAxisHelicoid
open Set Metric Bornology

def exteriorPlaneBase (R : ℝ) : Set (ℝ × ℝ) := {q | R < ‖q‖}

theorem exteriorPlaneBase_isOpen (R : ℝ) : IsOpen (exteriorPlaneBase R) :=
  isOpen_lt continuous_const continuous_norm

theorem exteriorPlaneBase_complement_isCompact (R : ℝ) :
    IsCompact (exteriorPlaneBase R)ᶜ := by
  have he : (exteriorPlaneBase R)ᶜ = closedBall (0 : ℝ × ℝ) R := by
    ext q
    simp [exteriorPlaneBase,Metric.mem_closedBall,dist_zero_right]
  rw [he]
  exact isCompact_closedBall _ _

theorem exteriorPlaneBase_isPreconnected {R : ℝ} (hR : 0 ≤ R) :
    IsPreconnected (exteriorPlaneBase R) := by
  have hs : IsPreconnected (sphere (0 : ℝ × ℝ) 1) :=
    isPreconnected_sphere (by norm_num) _ _
  have hc : IsPreconnected (Ioi R ×ˢ sphere (0 : ℝ × ℝ) 1) :=
    isPreconnected_Ioi.prod hs
  have hi := hc.image (fun q : ℝ × (ℝ × ℝ) => q.1 • q.2)
    (continuous_fst.smul continuous_snd).continuousOn
  have he : (fun q : ℝ × (ℝ × ℝ) => q.1 • q.2) ''
      (Ioi R ×ˢ sphere (0 : ℝ × ℝ) 1) = exteriorPlaneBase R := by
    ext q
    constructor
    · rintro ⟨⟨r,u⟩,⟨hr,hu⟩,rfl⟩
      have hr0 : 0 < r := hR.trans_lt hr
      have hu1 : ‖u‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hu
      change R < ‖r • u‖
      simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos hr0,hu1,mul_one,mem_Ioi] using hr
    · intro hq
      have hq0 : ‖q‖ ≠ 0 := (hR.trans_lt hq).ne'
      refine ⟨(‖q‖,‖q‖⁻¹ • q),⟨hq,?_⟩,?_⟩
      · simp [norm_smul,hq0]
      · simp [smul_smul,hq0]
  exact he ▸ hi

theorem exteriorPlaneBase_unbounded (R : ℝ) : ¬ IsBounded (exteriorPlaneBase R) := by
  intro hb
  obtain ⟨C,hC⟩ := hb.exists_norm_le
  let a := max (max R C) 0+1
  have ha : 0 < a := by dsimp [a]; linarith [le_max_right (max R C) 0]
  have hRa : R < a := by dsimp [a]; linarith [le_max_left R C,le_max_left (max R C) 0]
  have hCa : C < a := by dsimp [a]; linarith [le_max_right R C,le_max_left (max R C) 0]
  have hn : ‖(a,(0 : ℝ))‖ = a := by simp [Prod.norm_def,abs_of_pos ha,ha.le]
  have hm : (a,(0 : ℝ)) ∈ exteriorPlaneBase R := by change R < ‖(a,(0 : ℝ))‖; rwa [hn]
  have hh := hC _ hm
  rw [hn] at hh
  exact hCa.not_ge hh

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.exteriorPlaneBase_isPreconnected
