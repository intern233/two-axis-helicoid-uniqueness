import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Separation.Connected
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace TwoAxisHelicoid
open Complex Set
open scoped Topology

/-- An n-th power is injective on each connected subset lying over the
open right half-plane. A continuous branch of the normalized n-th root
is constant there because it takes values among finitely many roots. -/
theorem pow_injective_on_connected_right_half_plane {n : ℕ} (hn : 0<n) {S : Set ℂ}
    (connected : IsPreconnected S) (positive : ∀ z∈S,0<(z^n).re) : InjOn (fun z : ℂ => z^n) S := by
  classical
  let f := fun w : ℂ => exp (log w/(n:ℂ))
  let ratio := fun z : ℂ => z / f (z^n)
  have nz (w : ℂ) : f w≠0 := Complex.exp_ne_zero _
  have root {w : ℂ} (hw : w≠0) : f w^n=w := by
    have nc : (n:ℂ)≠0 := Nat.cast_ne_zero.mpr hn.ne'
    change exp (log w/(n:ℂ))^n=w
    rw [← Complex.exp_nat_mul,show (n:ℂ)*(log w/(n:ℂ))=log w by field_simp,Complex.exp_log hw]
  have cont : ContinuousOn ratio S := by
    intro z hz
    apply ContinuousAt.continuousWithinAt
    change ContinuousAt (fun w : ℂ => w/f (w^n)) z
    apply ContinuousAt.div (f := fun w : ℂ => w) (g := fun w : ℂ => f (w^n)) continuousAt_id _ (nz _)
    have cp : ContinuousAt (fun w : ℂ => w^n) z := continuousAt_id.pow n
    have cl : ContinuousAt (fun w : ℂ => log (w^n)) z := (continuousAt_clog (Or.inl (positive z hz))).comp (f := fun w : ℂ => w^n) cp
    exact continuous_exp.continuousAt.comp (cl.div_const (n:ℂ))
  have finite : (ratio '' S).Finite := by
    apply (Polynomial.nthRootsFinset n (1:ℂ)).finite_toSet.subset
    rintro _ ⟨z,hz,rfl⟩
    apply (Polynomial.mem_nthRootsFinset hn _).mpr
    have nonzero : z^n≠0 := fun e => (positive z hz).ne' (congrArg re e)
    change (z/f (z^n))^n=1
    rw [div_pow,root nonzero,div_self nonzero]
  have singleton := (connected.image _ cont).isDiscrete_iff_subsingleton.mp finite.isDiscrete
  intro z hz w hw eq
  have same := singleton (mem_image_of_mem ratio hz) (mem_image_of_mem ratio hw)
  change z/f (z^n)=w/f (w^n) at same
  change z^n=w^n at eq
  rw [eq] at same
  exact (div_left_inj' (nz _)).mp same

/-- Each sufficiently small punctured disk contains two different
points with the same positive real n-th power if n is greater than one. -/
theorem distinct_small_equal_positive_power {n : ℕ} (hn : 1<n) {δ : ℝ} (hδ : 0<δ) (B : ℝ) :
    ∃ z w : ℂ, z≠w ∧ 0<‖z‖ ∧ ‖z‖<δ ∧ 0<‖w‖ ∧ ‖w‖<δ ∧ z^n=w^n ∧ B<((z^n)⁻¹).re := by
  let ζ := exp (2*(Real.pi:ℂ)*I/n)
  have primitive : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n (by omega)
  have zn := primitive.pow_eq_one
  have norm : ‖ζ‖=1 := Complex.norm_eq_one_of_pow_eq_one zn (by omega)
  have notOne : ζ≠1 := by
    intro h
    have div := primitive.dvd_of_pow_eq_one 1 (by simp [h])
    exact hn.not_ge (Nat.le_of_dvd (by decide) div)
  obtain ⟨r,hr,rmin⟩ := exists_between (lt_min (lt_min hδ zero_lt_one) (inv_pos.mpr (show 0 < |B|+1 by positivity)))
  have rd := rmin.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have r1 : r<1 := rmin.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have rlim : r<(|B|+1)⁻¹ := rmin.trans_le (min_le_right _ _)
  have power : r^n≤r := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hr.le r1.le) hr.le).trans_eq (one_mul _)
  have big : B<(r^n)⁻¹ := lt_of_lt_of_le ((le_abs_self B).trans_lt (by linarith : |B| < |B|+1))
    (((lt_inv_comm₀ (by positivity : 0 < |B|+1) hr).mpr rlim).le.trans ((inv_le_inv₀ hr (pow_pos hr _)).mpr power))
  refine ⟨(r:ℂ),(r:ℂ)*ζ,?_,?_,?_,?_,?_,?_,?_⟩
  · intro eq
    exact notOne (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne') (eq.symm.trans (mul_one _).symm))
  · simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr] using hr
  · simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr] using rd
  · simpa only [norm_mul,norm,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr] using hr
  · simpa only [norm_mul,norm,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr] using rd
  · rw [mul_pow,zn,mul_one]
  · simpa only [← Complex.ofReal_pow,← Complex.ofReal_inv,Complex.ofReal_re] using big

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.pow_injective_on_connected_right_half_plane
#print axioms TwoAxisHelicoid.distinct_small_equal_positive_power
