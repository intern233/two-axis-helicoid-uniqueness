import TwoAxisHelicoid.SinglePunctureEndFlux
import TwoAxisHelicoid.EllipticRealNormalization
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
open scoped Interval Topology

/-- First marked period one, second period an arbitrary upper-half-plane
parameter. These are the periods used in Appendix C.1. -/
noncomputable def upperMarkedLattice (τ : ℂ) (upper : 0<τ.im) : PeriodPair where
  ω₁ := 1
  ω₂ := τ
  indep := by
    apply LinearIndependent.pair_iff.mpr
    intro a b h
    have im := congrArg Complex.im h
    have re := congrArg Complex.re h
    simp [Complex.real_smul,Complex.mul_re,Complex.mul_im] at im re
    have bz : b=0 := im.resolve_right upper.ne'
    exact ⟨by simpa only [bz,zero_mul,add_zero] using re,bz⟩

noncomputable def markedCellBase (L : PeriodPair) : ℂ := -(L.ω₁+L.ω₂)/2

/-- Oriented boundary in terms of genuine integrals along the two
marked generator directions. -/
theorem marked_cell_boundary (L : PeriodPair) (f : ℂ → ℂ) :
    let a := markedCellBase L
    punctureBoundaryIntegral L f 1 =
      ellipticLinePeriod f a L.ω₁+ellipticLinePeriod f (a+L.ω₁) L.ω₂-
        ellipticLinePeriod f (a+L.ω₂) L.ω₁-ellipticLinePeriod f a L.ω₂ := by
  let a := markedCellBase L
  have corner (s t : ℝ) : spinSquareLinear L s t=(s:ℂ)*L.ω₁+(t:ℂ)*L.ω₂ := by simp [spinSquareLinear,Complex.real_smul]
  have hA : spinSquareLinear L (-1/2) (-1/2)=a := by rw [corner]; dsimp [a,markedCellBase]; push_cast; ring
  have hB : spinSquareLinear L (1/2) (-1/2)=a+L.ω₁ := by rw [corner]; dsimp [a,markedCellBase]; push_cast; ring
  have hC : spinSquareLinear L (-1/2) (1/2)=a+L.ω₂ := by rw [corner]; dsimp [a,markedCellBase]; push_cast; ring
  have hD : spinSquareLinear L (1/2) (1/2)=a+L.ω₁+L.ω₂ := by rw [corner]; dsimp [a,markedCellBase]; push_cast; ring
  have edge (x d : ℂ) : dilatedEdgeIntegral f x (x+d) 1=ellipticLinePeriod f x d := by
    simp [dilatedEdgeIntegral,ellipticLinePeriod]
  change punctureBoundaryIntegral L f 1=_
  unfold punctureBoundaryIntegral
  simp only [hA,hB,hC,hD,edge]
  rw [show a+L.ω₁+L.ω₂=a+L.ω₂+L.ω₁ by ring,edge]

theorem marked_line_primitive {f F : ℂ → ℂ} {a d : ℂ}
    (der : ∀ t∈Icc (0:ℝ) 1, HasDerivAt F (f (a+(t:ℂ)*d)) (a+(t:ℂ)*d))
    (cont : ∀ t∈Icc (0:ℝ) 1, ContinuousAt f (a+(t:ℂ)*d)) :
    ellipticLinePeriod f a d=F (a+d)-F a := by
  let p := fun t : ℝ => a+(t:ℂ)*d
  have diff (t : ℝ) : HasDerivAt p d t := by
    have dr : HasDerivAt (fun u : ℝ => (u:ℂ)) 1 t := by
      simpa only [Complex.ofReal_one] using (hasDerivAt_id' t).ofReal_comp
    simpa only [p,one_mul] using (dr.mul_const d).const_add a
  have cp : Continuous p := by dsimp [p]; fun_prop
  have integral : IntervalIntegrable (fun t => d*f (p t)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    intro t ht
    exact (continuousAt_const.mul ((cont t ht).comp (f:=p) cp.continuousAt)).continuousWithinAt
  have law := intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=F ∘ p) (fun t ht => by
    rw [uIcc_of_le zero_le_one] at ht
    exact ((der t ht).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t (diff t)) integral
  simpa only [ellipticLinePeriod,p,Function.comp_apply,Complex.ofReal_one,one_mul,Complex.ofReal_zero,zero_mul,add_zero,
    smul_eq_mul] using law

/-- Exact residue of dz/z on the centered parallelogram, for every
upper-half-plane marking. On the left edge the logarithm of -z is
single-valued, and the endpoint changes of branch contribute 2πi. -/
theorem upper_marked_inverse_residue (τ : ℂ) (upper : 0<τ.im) :
    punctureBoundaryIntegral (upperMarkedLattice τ upper) (fun z : ℂ => z⁻¹) 1=2*(Real.pi:ℂ)*I := by
  let a : ℂ := -(1+τ)/2
  have imA : a.im= -τ.im/2 := by simp [a]
  have imB : (a+1).im= -τ.im/2 := by simp [imA]
  have rslit (s : ℝ) : a+1+(s:ℂ)*τ∈slitPlane := by
    by_cases h : s=1/2
    · rw [h,show a+1+((1/2:ℝ):ℂ)*τ=1/2 by dsimp [a]; push_cast; ring]
      exact mem_slitPlane_iff.mpr (Or.inl (by norm_num))
    · apply mem_slitPlane_iff.mpr ∘ Or.inr
      have e : (a+1+(s:ℂ)*τ).im=(s-1/2)*τ.im := by simp [imA,Complex.mul_im]; ring
      rw [e]
      exact mul_ne_zero (sub_ne_zero.mpr h) upper.ne'
  have straight (b d : ℂ) (slit : ∀ s : ℝ, b+(s:ℂ)*d∈slitPlane) :
      ellipticLinePeriod (fun z : ℂ => z⁻¹) b d=log (b+d)-log b :=
    marked_line_primitive (fun s _ => Complex.hasDerivAt_log (slit s))
      (fun s _ => continuousAt_id.inv₀ (slitPlane_ne_zero (slit s)))
  have bot := straight a 1 (fun s => mem_slitPlane_iff.mpr (Or.inr (by simp [imA]; linarith)))
  have top := straight (a+τ) 1 (fun s => mem_slitPlane_iff.mpr (Or.inr (by simp [imA]; linarith)))
  have right := straight (a+1) τ rslit
  have other (s : ℝ) : -(a+(s:ℂ)*τ)∈slitPlane := by
    rw [show -(a+(s:ℂ)*τ)=a+1+((1-s:ℝ):ℂ)*τ by dsimp [a]; push_cast; ring]
    exact rslit _
  have left : ellipticLinePeriod (fun z : ℂ => z⁻¹) a τ=log (-(a+τ))-log (-a) := by
    apply marked_line_primitive (F:=fun w => log (-w))
    · intro s _
      simpa only [Function.comp_def,id_eq,inv_neg,neg_mul,neg_one_mul,neg_neg,mul_neg_one]
        using (Complex.hasDerivAt_log (other s)).comp (a+(s:ℂ)*τ) (hasDerivAt_id' _).neg
    · intro s _
      exact continuousAt_id.inv₀ (neg_ne_zero.mp (slitPlane_ne_zero (other s)))
  have jump (z : ℂ) (negIm : z.im<0) : log (-z)=log z+(Real.pi:ℂ)*I := by
    simp only [Complex.log,norm_neg,Complex.arg_neg_eq_arg_add_pi_of_im_neg negIm,Complex.ofReal_add]
    ring
  rw [marked_cell_boundary]
  change ellipticLinePeriod _ a 1+ellipticLinePeriod _ (a+1) τ-ellipticLinePeriod _ (a+τ) 1-ellipticLinePeriod _ a τ=_
  rw [bot,right,top,left,show a+1+τ=a+τ+1 by ring]
  have b : a+τ= -(a+1) := by dsimp [a]; ring
  have aJump := jump a (by rw [imA]; linarith)
  have bJump := jump (a+1) (by rw [imB]; linarith)
  rw [b,neg_neg]
  linear_combination aJump+bJump

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_cell_boundary
#print axioms TwoAxisHelicoid.upper_marked_inverse_residue
