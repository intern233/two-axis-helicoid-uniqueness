import TwoAxisHelicoid.HeightEndEmbedding

namespace TwoAxisHelicoid
open Complex Filter Set Bornology Topology
open scoped Topology

/-- A compact parameter set gives a common spatial bound on the two
horizontal segments at imaginary height ±Y. -/
private theorem compact_end_segment_bound {T : Type*} [TopologicalSpace T]
    {K : Set T} (hK : IsCompact K) {X : T → ℂ → Fin 3 → ℝ} {R Y : ℝ}
    (hy : 0 ≤ Y) (hr : R<Y)
    (hc : ∀ k ∈ K, ∀ z : ℂ, R < ‖z‖ → ContinuousAt (fun p : T × ℂ => X p.1 p.2) (k,z))
    (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k ∈ K, ∀ x : ℝ, |x| ≤ M → ∀ ε ∈ ({-1,1} : Set ℝ),
      ∀ j : Fin 3, |X k ((x:ℂ)+I*((ε*Y:ℝ):ℂ)) j| ≤ C := by
  let V := K ×ˢ (Icc (-M) M ×ˢ ({-1,1} : Set ℝ))
  have hv : IsCompact V := hK.prod (isCompact_Icc.prod ((finite_singleton (1:ℝ)).insert (-1)).isCompact)
  let F := fun p : T × (ℝ × ℝ) => X p.1 ((p.2.1:ℂ)+I*((p.2.2*Y:ℝ):ℂ))
  have cf : ContinuousOn F V := by
    rintro ⟨k,x,ε⟩ ⟨hk,_,he⟩
    have absε : |ε*Y|=Y := by
      rcases (show ε=-1 ∨ ε=1 by simpa using he) with rfl | rfl <;> simp [abs_of_nonneg hy]
    have hn := hr.trans_le (absε ▸ vertical_line_norm_ge_abs x (ε*Y))
    exact ((hc k hk _ hn).comp (x := (k,x,ε)) (f := fun p : T × (ℝ × ℝ) => (p.1,(p.2.1:ℂ)+I*((p.2.2*Y:ℝ):ℂ))) (by fun_prop)).continuousWithinAt
  obtain ⟨C,hC,hb⟩ := (hv.image_of_continuousOn cf).isBounded.exists_pos_norm_le
  refine ⟨C,hC,?_⟩
  intro k hk x hx ε hε j
  have bound := hb _ ⟨(k,x,ε),⟨hk,abs_le.mp hx,hε⟩,rfl⟩
  simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (F (k,x,ε)) j).trans bound

/-- Uniform injectivity and uniform escape on an exterior height chart
over a compact parameter set. Only the imaginary part of the Gauss
correction is controlled, so adding any real logarithm of a positive
López–Ros multiplier preserves the phase hypothesis. -/
theorem compact_family_helicoidal_end_control {T : Type*} [TopologicalSpace T]
    {K : Set T} (hK : IsCompact K) (X : T → ℂ → Fin 3 → ℝ) (F : T → ℂ → ℂ) (α b R₀ Y : ℝ)
    (hy : 0 ≤ Y) (hRY : R₀ < Y)
    (hc : ∀ k ∈ K, ∀ z : ℂ, R₀ < ‖z‖ → ContinuousAt (fun p : T × ℂ => X p.1 p.2) (k,z))
    (hX : ∀ k ∈ K, ∀ z : ℂ, R₀ < ‖z‖ → HasFDerivAt (X k)
      (nullRealDerivative (weierstrassTriple (exp (I*α*z+F k z)) 1)) z)
    (hheight : ∀ k ∈ K, ∀ z : ℂ, R₀ < ‖z‖ → X k z 2 = z.re+b)
    (hF : ∀ k ∈ K, ∀ z : ℂ, Y ≤ ‖z‖ → |(F k z).im| ≤ 1) :
    (∃ R : ℝ, R₀ < R ∧ ∀ k ∈ K, InjOn (X k) {z : ℂ | R ≤ ‖z‖}) ∧
    (∀ B : ℝ, 0 ≤ B → ∃ D : ℝ, 0 < D ∧ ∀ k ∈ K, ∀ z : ℂ, R₀ < ‖z‖ → ‖X k z‖ ≤ B → ‖z‖ ≤ D) := by
  have coordinates (z : ℂ) : (z.re:ℂ)+I*z.im=z := by simpa [mul_comm] using Complex.re_add_im z
  constructor
  · obtain ⟨C,hC,hseg⟩ := compact_end_segment_bound hK hy hRY hc Y
    let R := max (R₀+1) (2*Y+2*(2*C)+1)
    have hR : R₀ < R := by dsimp [R]; linarith [le_max_left (R₀+1) (2*Y+2*(2*C)+1)]
    refine ⟨R,hR,?_⟩
    intro k hk z hz w hw same
    have hx : z.re=w.re := by
      have eq := congrFun same 2
      rw [hheight k hk z (hR.trans_le hz),hheight k hk w (hR.trans_le hw)] at eq
      linarith
    have cw : (z.re:ℂ)+I*w.im=w := by rw [hx,coordinates]
    apply Complex.ext hx
    apply height_end_level_injective α z.re R₀ Y (2*C) hRY (by positivity) (hX k hk) (hF k hk)
    · intro small
      have plus := hseg k hk z.re small 1 (by simp)
      have minus := hseg k hk z.re small (-1) (by simp)
      simp only [one_mul] at plus
      simp only [neg_one_mul,Complex.ofReal_neg] at minus
      exact ⟨endHorizontalSupport_bound _ (plus 0) (plus 1),endHorizontalSupport_bound _ (minus 0) (minus 1)⟩
    · rw [coordinates]
      exact (le_max_right _ _).trans hz
    · rw [cw]
      exact (le_max_right _ _).trans hw
    · rwa [coordinates,cw]
  · intro B hB
    let M := B+|b|
    obtain ⟨C,hC,hseg⟩ := compact_end_segment_bound hK hy hRY hc M
    refine ⟨M+Y+4*(B+C)+1,by dsimp [M]; positivity,?_⟩
    intro k hk z hz bound
    have hb (j : Fin 3) : |X k z j| ≤ B := (norm_le_pi_norm _ j).trans bound
    have x : |z.re| ≤ M := by
      calc |z.re| = |X k z 2-b| := by rw [hheight k hk z hz]; congr 1; ring
           _ ≤ |X k z 2|+|b| := abs_sub _ _
           _ ≤ M := add_le_add (hb 2) (le_refl _)
    have y := height_end_vertical_escape_bound α z.re R₀ Y B C hy hRY hB hC.le (hX k hk) (hF k hk)
      (fun ε he => by
        rw [← Complex.ofReal_mul]
        exact ⟨hseg k hk z.re x ε he 0,hseg k hk z.re x ε he 1⟩)
      (y := z.im) (by rw [coordinates]; exact hb 0) (by rw [coordinates]; exact hb 1)
    linarith [Complex.norm_le_abs_re_add_abs_im z]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_family_helicoidal_end_control
