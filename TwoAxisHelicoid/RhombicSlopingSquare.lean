import TwoAxisHelicoid.RhombicCenteredRectangle
import TwoAxisHelicoid.OriginalSlopingPeriod

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

/-- The physical period of the sloping generator and its conjugate
are an integral basis of the original marked rhombic lattice. -/
theorem rhombic_sloping_generator_basis {t : ℝ} (ht : 0<t) (z : ℂ) :
    z∈(rhombicPeriodPair t ht).lattice ↔ ∃ j k : ℤ, z=j*(1-I*t)+k*(1+I*t) := by
  rw [rhombic_mem_lattice_iff]
  constructor
  · rintro ⟨m,n,hr,hi⟩
    refine ⟨m,m+n,Complex.ext ?_ ?_⟩ <;> simp [mul_re,mul_im,hr,hi] <;> ring
  · rintro ⟨j,k,rfl⟩
    refine ⟨j,k-j,?_,?_⟩ <;> simp [mul_re,mul_im] <;> ring

noncomputable def rhombicSlopingPoint (t u v : ℝ) : ℂ :=
  -1+(u:ℂ)*(1-I*t)+(v:ℂ)*(1+I*t)

theorem rhombicSlopingPoint_parts (t u v : ℝ) :
    (rhombicSlopingPoint t u v).re= -1+u+v ∧ (rhombicSlopingPoint t u v).im=(v-u)*t := by
  constructor <;> simp [rhombicSlopingPoint,mul_re,mul_im]
  ring

/-- Representatives in the fundamental square spanned by the two
sloping cycles. In the half-open square every torus point has exactly
one representative. -/
theorem rhombic_sloping_square_rep {t : ℝ} (ht : 0<t) (z : ℂ) :
    ∃ u∈Ico (0:ℝ) 1, ∃ v∈Ico (0:ℝ) 1, z-rhombicSlopingPoint t u v∈(rhombicPeriodPair t ht).lattice := by
  let U := (z.re+1-z.im/t)/2
  let V := (z.re+1+z.im/t)/2
  let j : ℤ := ⌊U⌋
  let k : ℤ := ⌊V⌋
  let u := U-j
  let v := V-k
  have bounds (x : ℝ) : x-⌊x⌋∈Ico (0:ℝ) 1 := ⟨sub_nonneg.mpr (Int.floor_le x),by linarith [Int.lt_floor_add_one x]⟩
  have e : z=rhombicSlopingPoint t U V := by
    apply Complex.ext
    · rw [(rhombicSlopingPoint_parts ..).1]
      dsimp [U,V]
      ring
    · rw [(rhombicSlopingPoint_parts ..).2]
      dsimp [U,V]
      field_simp [ht.ne']
      ring
  refine ⟨u,bounds U,v,bounds V,(rhombic_sloping_generator_basis ht _).mpr ⟨j,k,?_⟩⟩
  calc
    z-rhombicSlopingPoint t u v=rhombicSlopingPoint t U V-rhombicSlopingPoint t u v := congrArg (fun w => w-rhombicSlopingPoint t u v) e
    _=_ := by dsimp [rhombicSlopingPoint,u,v]; push_cast; ring

theorem rhombic_sloping_square_injective {t u v x y : ℝ} (ht : 0<t)
    (hu : u∈Ico (0:ℝ) 1) (hv : v∈Ico (0:ℝ) 1) (hx : x∈Ico (0:ℝ) 1) (hy : y∈Ico (0:ℝ) 1)
    (eq : periodTorusProjection (rhombicPeriodPair t ht) (rhombicSlopingPoint t u v)=
      periodTorusProjection (rhombicPeriodPair t ht) (rhombicSlopingPoint t x y)) : u=x ∧ v=y := by
  obtain ⟨j,k,al⟩ := (rhombic_sloping_generator_basis ht _).mp ((periodTorusProjection_eq_iff _ _ _).mp eq)
  have real := congrArg re al
  have imag := congrArg im al
  simp only [sub_re,(rhombicSlopingPoint_parts ..).1,add_re,mul_re,intCast_re,intCast_im,zero_mul,sub_zero,
    one_re,ofReal_re,ofReal_im,I_re,I_im,add_zero,mul_zero,mul_one] at real
  simp only [sub_im,(rhombicSlopingPoint_parts ..).2,add_im,mul_im,intCast_re,intCast_im,zero_mul,add_zero,
    one_im,ofReal_re,ofReal_im,I_re,I_im,zero_sub,zero_add,one_mul,mul_zero] at imag
  have diff : y-v-(x-u)=(k:ℝ)-j := by
    apply (mul_left_inj' ht.ne').mp
    linarith only [imag]
  have jj : (j:ℝ)=x-u := by linarith
  have kk : (k:ℝ)=y-v := by linarith
  have zero {i : ℤ} {q r : ℝ} (hq : q∈Ico (0:ℝ) 1) (hr : r∈Ico (0:ℝ) 1) (h : (i:ℝ)=q-r) : i=0 := by
    have low : (-1:ℤ) < i := by exact_mod_cast (show (-1:ℝ) < (i:ℝ) by linarith [hq.1,hr.2])
    have high : i<(1:ℤ) := by exact_mod_cast (show (i:ℝ)<1 by linarith [hq.2,hr.1])
    omega
  rw [zero hx hu jj,Int.cast_zero] at jj
  rw [zero hy hv kk,Int.cast_zero] at kk
  constructor <;> linarith

/-- The four open triangles cut by the axes in the square are permuted
by the genuine sign and conjugation symmetries. One triangle represents
all four without changing the period scale. -/
theorem rhombic_sloping_open_triangle {t u v : ℝ} (hu : u∈Ioo (0:ℝ) 1) (hv : v∈Ioo (0:ℝ) 1)
    (diag : u≠v) (cross : u+v≠1) :
    let z := rhombicSlopingPoint t u v
    ∃ x y : ℝ, 0<y ∧ y<x ∧ x+y<1 ∧
      (rhombicSlopingPoint t x y=z ∨ rhombicSlopingPoint t x y=conj z ∨
        rhombicSlopingPoint t x y= -z ∨ rhombicSlopingPoint t x y= -conj z) := by
  intro z
  have swap (a b : ℝ) : rhombicSlopingPoint t b a=conj (rhombicSlopingPoint t a b) := by
    apply Complex.ext <;> simp only [conj_re,conj_im,(rhombicSlopingPoint_parts ..).1,(rhombicSlopingPoint_parts ..).2] <;> ring
  have rev (a b : ℝ) : rhombicSlopingPoint t (1-a) (1-b)= -rhombicSlopingPoint t a b := by
    dsimp [rhombicSlopingPoint]; push_cast; ring
  rcases lt_or_gt_of_ne cross with low|high <;> rcases lt_or_gt_of_ne diag with uv|vu
  · exact ⟨v,u,hu.1,uv,by linarith,Or.inr (Or.inl (swap u v))⟩
  · exact ⟨u,v,hv.1,vu,low,Or.inl rfl⟩
  · exact ⟨1-u,1-v,by linarith [hv.2],by linarith,by linarith,Or.inr (Or.inr (Or.inl (rev u v)))⟩
  · exact ⟨1-v,1-u,by linarith [hu.2],by linarith,by linarith,Or.inr (Or.inr (Or.inr ((rev v u).trans (congrArg Neg.neg (swap u v)))))⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rhombic_sloping_square_injective
#print axioms TwoAxisHelicoid.rhombic_sloping_open_triangle
