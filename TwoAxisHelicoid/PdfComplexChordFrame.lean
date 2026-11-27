import TwoAxisHelicoid.PdfComplexChordCoordinates

namespace TwoAxisHelicoid.PdfVertical
open Complex

structure ComplexChordFrame where
  u : CGrid
  x : CGrid
  reciprocal : CGrid
  minusNormSq : Grid
  plusNormSq : Grid

def complexChordFrame (p : ChordParams) (S V : Grid) : ComplexChordFrame :=
  let one := Grid.ofInt 1
  let two := Grid.ofInt 2
  let dx := p.k.mul V
  let r := p.h.sub dx
  let y := p.k.mul S
  let n := (((p.k.squared.mul (one.sub S)).mul (one.add S)).neg.add dx.squared).sub ((two.mul p.h).mul dx)
  let d := r.squared.add (y.sub one).squared
  let b := r.squared.add (y.add one).squared
  ⟨⟨r,y⟩,⟨n.divPos d,(two.mul r).divPos d⟩,⟨n.divPos b,(two.mul r).neg.divPos b⟩,d,b⟩

def ComplexChordFrame.Sound (f : ComplexChordFrame) (t : ℝ) (z : ℂ) : Prop :=
  let u := jacobiChordPoint t z
  f.u.Contains u ∧ f.x.Contains (jacobiChordX u) ∧ f.reciprocal.Contains (jacobiChordX u)⁻¹ ∧
    f.minusNormSq.Contains (normSq (u-I)) ∧ f.plusNormSq.Contains (normSq (u+I))

theorem complexChordFrame_sound {p : ChordParams} {t a : ℝ} (data : p.Sound t a)
    {S V : Grid} {z : ℂ} (hs : S.Contains z.re) (hv : V.Contains z.im) :
    (complexChordFrame p S V).Sound t z := by
  let h := leftChordH (leftNome t)
  let k := leftChordK (leftNome t)
  let dx := k*z.im
  let r := h-dx
  let y := k*z.re
  have one : (Grid.ofInt 1).Contains 1 := by simpa only [Int.cast_one] using Grid.contains_int 1
  have two : (Grid.ofInt 2).Contains 2 := by simpa only [Int.cast_ofNat] using Grid.contains_int 2
  have ox := Grid.contains_mul data.k hv
  have rr := Grid.contains_sub data.h ox
  have yy := Grid.contains_mul data.k hs
  have n := Grid.contains_sub (Grid.contains_add
    (Grid.contains_neg (Grid.contains_mul (Grid.contains_mul (Grid.contains_squared data.k)
      (Grid.contains_sub one hs)) (Grid.contains_add one hs))) (Grid.contains_squared ox))
      (Grid.contains_mul (Grid.contains_mul two data.h) ox)
  have d := Grid.contains_add (Grid.contains_squared rr) (Grid.contains_squared (Grid.contains_sub yy one))
  have b := Grid.contains_add (Grid.contains_squared rr) (Grid.contains_squared (Grid.contains_add yy one))
  have pos := Grid.contains_mul two rr
  have u : jacobiChordPoint t z=(⟨r,y⟩:ℂ) := complex_chord_point_coordinates t z
  have eq := complex_chord_coordinates (leftChordH_sq_add_K_sq (leftNome t)) z.re z.im
  unfold ComplexChordFrame.Sound
  rw [u]
  refine ⟨⟨rr,yy⟩,?_,?_,?_,?_⟩
  · rw [eq.1]
    exact ⟨Grid.contains_div n d, Grid.contains_div pos d⟩
  · rw [eq.2]
    exact ⟨Grid.contains_div n b,by
      simpa only [complexChordFrame,neg_mul] using Grid.contains_div (Grid.contains_neg pos) b⟩
  · simpa only [normSq_apply,sub_re,sub_im,I_re,I_im,sub_zero,pow_two,r,y,h,k,dx,complexChordFrame] using d
  · simpa only [normSq_apply,add_re,add_im,I_re,I_im,add_zero,pow_two,r,y,h,k,dx,complexChordFrame] using b

def ComplexChordFrame.regular (f : ComplexChordFrame) (p : ChordParams) : Bool :=
  let A := f.x.scale p.q
  let B := f.reciprocal.scale p.q
  decide (f.minusNormSq.ok=true ∧ 0<f.minusNormSq.lo ∧ f.plusNormSq.ok=true ∧ 0<f.plusNormSq.lo ∧
    A.ok=true ∧ A.mag<Grid.denom ∧ B.ok=true ∧ B.mag<Grid.denom)

theorem ComplexChordFrame.region {p : ChordParams} {t a : ℝ} (data : p.Sound t a) (ht : 0<t)
    {f : ComplexChordFrame} {z : ℂ} (frame : f.Sound t z) (valid : f.regular p=true) :
    let u := jacobiChordPoint t z
    let Q := jacobiNome (1/t)
    let x := jacobiChordX u
    u-I≠0 ∧ u+I≠0 ∧ ‖Q‖*‖x‖<1 ∧ ‖Q‖*‖x⁻¹‖<1 := by
  obtain ⟨_,x,recip,minus,plus⟩ := frame
  obtain ⟨om,pm,op,pp,oa,pa,ob,pb⟩ := of_decide_eq_true valid
  have positive {g : Grid} {w : ℂ} (h : g.Contains (normSq w)) (o : g.ok=true) (p0 : 0<g.lo) : w≠0 := by
    intro zero
    have lower := (h o).1
    rw [zero] at lower
    simp only [map_zero,mul_zero] at lower
    exact (not_lt_of_ge lower) (by exact_mod_cast p0)
  have small {g : CGrid} {w : ℂ} (h : g.Contains w) (ok : g.ok=true) (lim : g.mag<Grid.denom) : ‖w‖<1 := by
    apply (CGrid.norm_le_mag h ok).trans_lt
    rw [Grid.value,div_lt_iff₀ Grid.real_denom_pos,one_mul]
    exact_mod_cast lim
  have qEq : ((-(leftNome t)^2:ℝ):ℂ)=jacobiNome (1/t) := by
    simpa only [Complex.ofReal_neg] using (jacobiNome_inverse_eq_leftNome ht).symm
  refine ⟨positive minus om pm,positive plus op pp,?_,?_⟩
  · rw [← norm_mul,← qEq]
    exact small (CGrid.contains_scale data.q x) oa pa
  · rw [← norm_mul,← qEq]
    exact small (CGrid.contains_scale data.q recip) ob pb

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.complexChordFrame_sound
#print axioms TwoAxisHelicoid.PdfVertical.ComplexChordFrame.region

