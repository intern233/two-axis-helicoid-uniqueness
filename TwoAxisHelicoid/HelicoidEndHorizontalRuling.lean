import TwoAxisHelicoid.CertifiedC1HelicoidEnd
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace TwoAxisHelicoid
open Real Set Filter Bornology Metric
open scoped Topology

/-- A horizontal line on a surface which is a decaying single graph over
the standard helicoid must be a ruling at its own height. This establishes
the phase alignment before invoking any intersection theorem. -/
theorem HasHelicoidC1End.horizontal_line_is_ruling {M : Type*} [TopologicalSpace M]
    {Y : M → HelicoidTubeCoordinates} (hY : Continuous Y) (hEnd : HasHelicoidC1End Y)
    {h : ℝ} (hline : ∀ x : ℝ, ((x,0),h) ∈ range Y) : Real.sin h = 0 := by
  obtain ⟨C,_hC,R,_hR,hcompact,E,_he,u,_hsmooth,hgraph,hdecay⟩ := hEnd
  let D := helicoidProjectedEnd Y C (exteriorPlaneBase R)
  have hcore : IsCompact (Y '' Dᶜ) := hcompact.image hY
  obtain ⟨L,hL⟩ := hcore.isBounded.exists_norm_le
  by_contra hn
  let ε := |Real.sin h|/4
  have hε : 0 < ε := div_pos (abs_pos.mpr hn) (by norm_num)
  obtain ⟨T,_hT,hT⟩ := ((hasBasis_cobounded_norm.comap
    (Subtype.val : exteriorPlaneBase R → ℝ × ℝ)).eventually_iff).mp (hdecay.eventually_lt_const hε)
  let A := closedBall (0 : ℝ × ℝ) T
  have hcompactA : IsCompact (helicoidHeightBlock (1/2) A) :=
    helicoidHeightBlock_isCompact _ (isCompact_closedBall _ _)
  obtain ⟨B,hB⟩ := hcompactA.isBounded.exists_norm_le
  let x := max (max L B) 3+1
  obtain ⟨q,hq⟩ := hline x
  have hx : x ≤ ‖Y q‖ := by
    rw [hq]
    change x ≤ max (max ‖x‖ ‖(0 : ℝ)‖) ‖h‖
    exact (le_abs_self x).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hDL : q ∈ D := by
    by_contra h
    have hh := hL (Y q) ⟨q,h,rfl⟩
    dsimp [x] at hx
    linarith [le_max_left L B,le_max_left (max L B) 3]
  let p := E ⟨q,hDL⟩
  have he : Y q = helicoidTubeMap ((u p,p.1.1),p.1.2) := by
    simpa only [p,E.symm_apply_apply] using (hgraph p).2
  have hpT : T ≤ ‖p.1‖ := by
    by_contra! hn'
    have hpA : p.1 ∈ A := by simpa [A,dist_zero_right] using hn'.le
    have hmem : Y q ∈ helicoidHeightBlock (1/2) A :=
      ⟨(u p,p.1),⟨abs_le.mp (hgraph p).1,hpA⟩,he.symm⟩
    have hh := hB _ hmem
    dsimp [x] at hx
    linarith [le_max_right L B,le_max_left (max L B) 3]
  have hs : |u p| < ε := by
    have hh := hT (show p ∈ (Subtype.val : exteriorPlaneBase R → ℝ × ℝ) ⁻¹' {z | T ≤ ‖z‖} from hpT)
    change |u p| + helicoidGraphGradientNorm (extendOpenScalar u) p.1 < ε at hh
    exact lt_of_le_of_lt (le_add_of_nonneg_right (Real.sqrt_nonneg _)) hh
  have hvec := congrArg tubeCartesian (hq.symm.trans he)
  rw [tubeCartesian_normalMap] at hvec
  have hd (j : Fin 3) : |(![x,0,h] : Fin 3 → ℝ) j-standardHelicoid p.1.1 p.1.2 j| ≤ |u p| := by
    have heq := congrFun hvec j
    change (![x,0,h] : Fin 3 → ℝ) j = standardHelicoid p.1.1 p.1.2 j+u p*standardHelicoidNormal p.1.1 p.1.2 j at heq
    have hbound : |standardHelicoidNormal p.1.1 p.1.2 j| ≤ 1 := by
      have hsq := Finset.single_le_sum (f := fun k : Fin 3 => (standardHelicoidNormal p.1.1 p.1.2 k)^2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
      rw [(standardHelicoid_unit_normal _ _).1] at hsq
      nlinarith [sq_abs (standardHelicoidNormal p.1.1 p.1.2 j),abs_nonneg (standardHelicoidNormal p.1.1 p.1.2 j)]
    rw [heq,add_sub_cancel_left,abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) hbound
  let r := p.1.1
  let θ := p.1.2
  have hd0 := hd 0
  have hd1 := hd 1
  have hd2 := hd 2
  change |x-r*Real.cos θ| ≤ |u p| at hd0
  change |0-r*Real.sin θ| ≤ |u p| at hd1
  change |h-θ| ≤ |u p| at hd2
  rw [zero_sub,abs_neg,abs_mul] at hd1
  have hr : 1 ≤ |r| := by
    have hl : r*Real.cos θ ≤ |r| :=
      (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _))
    have hx3 : 3 ≤ x := by dsimp [x]; linarith [le_max_right (max L B) 3]
    linarith [(abs_le.mp hd0).2,(hgraph p).1]
  have hsin : |Real.sin θ| ≤ |u p| := (le_mul_of_one_le_left (abs_nonneg _) hr).trans hd1
  have hsh : |Real.sin h| ≤ |Real.sin h-Real.sin θ|+|Real.sin θ| := by
    simpa only [sub_add_cancel] using abs_add_le (Real.sin h-Real.sin θ) (Real.sin θ)
  dsimp [ε] at hs
  linarith only [hsh,(Real.abs_sin_sub_sin_le h θ).trans hd2,hsin,hs,abs_nonneg (Real.sin h)]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HasHelicoidC1End.horizontal_line_is_ruling
