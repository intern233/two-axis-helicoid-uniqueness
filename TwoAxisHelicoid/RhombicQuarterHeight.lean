import TwoAxisHelicoid.WeierstrassFibers
import TwoAxisHelicoid.WeierstrassAllMonotone
import TwoAxisHelicoid.RhombicPrimitivePatches
import TwoAxisHelicoid.PositiveFromSimpleZero

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology ComplexConjugate

/-- A finite value of ℘ cannot be real in the interior of the first
rhombic rectangle. Its two possible conjugate lifts would place the
height or the abscissa on one of the four boundary lines. -/
theorem rhombic_weierstrassP_quarter_im_ne {t : ℝ} (ht : 0<t) {z : ℂ}
    (hx : z.re∈Ioo (0:ℝ) 1) (hy : z.im∈Ioo 0 t) :
    ((rhombicPeriodPair t ht).weierstrassP z).im≠0 := by
  let L := rhombicPeriodPair t ht
  have off : z∉L.lattice := rhombic_horizontal_strip_not_mem ht hy
  have co : conj z∉L.lattice := fun h => off (by simpa using rhombic_conj_mem ht h)
  intro zero
  have eq : L.weierstrassP (conj z)=L.weierstrassP z := by
    rw [rhombic_weierstrassP_conj]
    apply Complex.ext
    · rfl
    · simpa only [Complex.conj_im] using (show -(L.weierstrassP z).im=(L.weierstrassP z).im by rw [zero,neg_zero])
  rcases (rhombic_weierstrassP_eq_iff ht off co).mp eq with h|h
  · obtain ⟨m,n,real,imag⟩ := (rhombic_mem_lattice_iff ht _).mp h
    simp only [sub_re,conj_re,sub_self,sub_im,conj_im] at real imag
    have n' : (n:ℝ)= -2*m := by linarith
    rw [n'] at imag
    have y : z.im=(m:ℝ)*t := by linarith
    have lo : (0:ℤ)<m := by exact_mod_cast (pos_of_mul_pos_left (y ▸ hy.1) ht.le)
    have hi : m<(1:ℤ) := by exact_mod_cast ((mul_lt_mul_iff_left₀ ht).mp (show (m:ℝ)*t<1*t by simpa [← y] using hy.2))
    omega
  · obtain ⟨m,n,real,imag⟩ := (rhombic_mem_lattice_iff ht _).mp h
    simp only [add_re,conj_re,add_im,conj_im,neg_add_cancel] at real imag
    have n' : (n:ℝ)=0 := (mul_eq_zero.mp imag.symm).resolve_right ht.ne'
    have x : z.re=(m:ℝ) := by linarith
    have lo : (0:ℤ)<m := by exact_mod_cast (x ▸ hx.1)
    have hi : m<(1:ℤ) := by exact_mod_cast (x ▸ hx.2)
    omega

/-- In the entire open parameter rectangle, for every positive lattice
height, ℘ has strictly negative imaginary part. -/
theorem rhombic_weierstrassP_quarter_im_neg {t x y : ℝ} (ht : 0<t)
    (hx : x∈Ioo (0:ℝ) 1) (hy : y∈Ioo 0 t) :
    ((rhombicPeriodPair t ht).weierstrassP ((x:ℂ)+I*y)).im<0 := by
  let L := rhombicPeriodPair t ht
  let z := fun s : ℝ => (x:ℂ)+I*s
  let h := fun s : ℝ => -(L.weierstrassP (z s)).im
  have re (s : ℝ) : (z s).re=x := by simp [z]
  have im (s : ℝ) : (z s).im=s := by simp [z]
  have dz (s : ℝ) : HasDerivAt z I s := by
    simpa [z] using ((((hasDerivAt_id s).ofReal_comp).const_mul I).const_add (x:ℂ))
  have hz : z 0=(x:ℂ) := by simp [z]
  have off : (x:ℂ)∉L.lattice := real_not_mem_rhombic_lattice_of_pos ht hx.1 (hx.2.trans (by norm_num))
  have d := rhombic_weierstrassP_hasDerivAt ht off
  have D := Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 (d.scomp_of_eq 0 (dz 0) hz.symm)
  have step : HasDerivAt h (-(L.derivWeierstrassP x).re) 0 := by
    simpa [h,L,Function.comp_def,smul_eq_mul,Complex.mul_im] using! D.neg
  apply neg_pos.mp
  apply positive_on_interval_of_simple_zero (f:=h) (b:=t) _ _ step
    (neg_pos.mpr (rhombic_weierstrassP_derivative_real_neg_of_pos ht ht hx.1 hx.2)) _ hy
  · intro s hs
    have o : z s∉L.lattice := rhombic_horizontal_strip_not_mem ht (by change (z s).im∈Ioo 0 t; rwa [im])
    exact ((Complex.continuous_im.continuousAt.comp ((L.analyticOnNhd_weierstrassP _ o).continuousAt.comp (dz s).continuousAt)).neg).continuousWithinAt
  · simp only [h,hz,rhombic_weierstrassP_real ht x,neg_zero,L]
  · intro s hs
    exact neg_ne_zero.mpr (rhombic_weierstrassP_quarter_im_ne ht ((re s).symm ▸ hx) ((im s).symm ▸ hs))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rhombic_weierstrassP_quarter_im_neg
