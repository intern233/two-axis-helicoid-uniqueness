import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace TwoAxisHelicoid
open Set

/-- The unique nonnegative pair with product s and difference d. This
parametrization is jointly continuous even when the hyperbola degenerates
to two coordinate rays at zero. -/
noncomputable def saddleQuadrantPair (s d : ℝ) : ℝ × ℝ :=
  ((Real.sqrt (d^2+4*s)+d)/2,(Real.sqrt (d^2+4*s)-d)/2)

theorem saddleQuadrantPair_characterization {s d : ℝ} (hs : 0≤s) :
    let p := saddleQuadrantPair s d
    0≤p.1 ∧ 0≤p.2 ∧ p.1*p.2=s ∧ p.1-p.2=d := by
  have le : |d|≤Real.sqrt (d^2+4*s) := by
    rw [← Real.sqrt_sq_eq_abs d]
    apply Real.sqrt_le_sqrt
    linarith
  have sq := Real.sq_sqrt (show 0≤d^2+4*s by positivity)
  dsimp only [saddleQuadrantPair]
  refine ⟨by linarith [neg_le_abs d],by linarith [le_abs_self d],?_,by ring⟩
  nlinarith only [sq]

theorem saddleQuadrantPair_of_point {x y : ℝ} (hx : 0≤x) (hy : 0≤y) :
    saddleQuadrantPair (x*y) (x-y)=(x,y) := by
  have root : Real.sqrt ((x-y)^2+4*(x*y))=x+y := by
    rw [show (x-y)^2+4*(x*y)=(x+y)^2 by ring,Real.sqrt_sq (add_nonneg hx hy)]
  apply Prod.ext <;> dsimp only [saddleQuadrantPair] <;> rw [root] <;> ring

/-- The parameter runs from the upper side to the right side of the
positive quadrant of the square of radius r. -/
noncomputable def saddleSquareArc (r s t : ℝ) : ℝ × ℝ :=
  saddleQuadrantPair s ((r-s/r)*t)

theorem saddleSquareArc_continuous (r : ℝ) :
    Continuous (fun q : ℝ × ℝ => saddleSquareArc r q.1 q.2) := by
  unfold saddleSquareArc saddleQuadrantPair
  fun_prop

theorem saddleSquareArc_endpoints {r s : ℝ} (hr : 0<r) (hs : 0≤s) :
    saddleSquareArc r s (-1)=(s/r,r) ∧ saddleSquareArc r s 1=(r,s/r) := by
  have non := div_nonneg hs hr.le
  constructor
  · have h := saddleQuadrantPair_of_point non hr.le
    rw [div_mul_cancel₀ _ hr.ne'] at h
    simpa only [saddleSquareArc,mul_neg_one,neg_sub] using h
  · have h := saddleQuadrantPair_of_point hr.le non
    rw [show r*(s/r)=s by field_simp] at h
    simpa only [saddleSquareArc,mul_one] using h

/-- The whole quadrant hyperbola in the square, including the broken
pair of radii at s=0, has one interval of parameters. -/
theorem saddleSquareArc_image {r s : ℝ} (hr : 0<r) (hs : 0≤s) (small : s<r^2) :
    saddleSquareArc r s '' Icc (-1:ℝ) 1=
      {p | p.1∈Icc 0 r ∧ p.2∈Icc 0 r ∧ p.1*p.2=s} := by
  have width : 0<r-s/r := sub_pos.mpr ((div_lt_iff₀ hr).mpr (by simpa only [pow_two] using small))
  have rdiv : r*(s/r)=s := by field_simp
  ext p
  constructor
  · rintro ⟨t,ht,rfl⟩
    let p := saddleSquareArc r s t
    obtain ⟨px,py,prod,diff⟩ := saddleQuadrantPair_characterization (d:=(r-s/r)*t) hs
    change 0≤p.1 at px
    change 0≤p.2 at py
    change p.1*p.2=s at prod
    change p.1-p.2=(r-s/r)*t at diff
    have upper : p.1-p.2≤r-s/r := by rw [diff]; simpa only [mul_one] using mul_le_mul_of_nonneg_left ht.2 width.le
    have lower : -(r-s/r)≤p.1-p.2 := by rw [diff]; simpa only [mul_neg_one] using mul_le_mul_of_nonneg_left ht.1 width.le
    have left : p.1≤r := by
      by_contra! gt
      have neg := mul_neg_of_neg_of_pos (sub_neg.mpr gt) (add_pos_of_pos_of_nonneg hr py)
      nlinarith only [neg,mul_le_mul_of_nonneg_left upper hr.le,prod,rdiv]
    have right : p.2≤r := by
      by_contra! gt
      have neg := mul_neg_of_neg_of_pos (sub_neg.mpr gt) (add_pos_of_pos_of_nonneg hr px)
      nlinarith only [neg,mul_le_mul_of_nonneg_left lower hr.le,prod,rdiv]
    exact ⟨⟨px,left⟩,⟨py,right⟩,prod⟩
  · rintro ⟨hx,hy,eq⟩
    let t := (p.1-p.2)/(r-s/r)
    have lo := mul_nonneg (sub_nonneg.mpr hy.2) (add_nonneg hr.le hx.1)
    have hi := mul_nonneg (sub_nonneg.mpr hx.2) (add_nonneg hr.le hy.1)
    have rt : (r-s/r)*t=p.1-p.2 := by dsimp [t]; field_simp [width.ne']
    refine ⟨t,⟨(le_div_iff₀ width).mpr ?_,(div_le_iff₀ width).mpr ?_⟩,?_⟩
    · apply (mul_le_mul_iff_right₀ hr).mp
      nlinarith only [lo,eq,rdiv]
    · apply (mul_le_mul_iff_right₀ hr).mp
      nlinarith only [hi,eq,rdiv]
    · rw [saddleSquareArc,rt,← eq]
      exact saddleQuadrantPair_of_point hx.1 hy.1

theorem saddleSquareArc_injective {r s : ℝ} (hr : 0<r) (hs : 0≤s) (small : s<r^2) :
    Function.Injective (saddleSquareArc r s) := by
  have w := sub_ne_zero.mpr ((div_lt_iff₀ hr).mpr (by simpa only [pow_two] using small)).ne'
  intro t u eq
  have p := (saddleQuadrantPair_characterization (d:=(r-s/r)*t) hs).2.2.2
  have q := (saddleQuadrantPair_characterization (d:=(r-s/r)*u) hs).2.2.2
  have h := congrArg (fun z : ℝ×ℝ => z.1-z.2) eq
  exact mul_left_cancel₀ w (p.symm.trans (h.trans q))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.saddleSquareArc_image
#print axioms TwoAxisHelicoid.saddleSquareArc_injective

