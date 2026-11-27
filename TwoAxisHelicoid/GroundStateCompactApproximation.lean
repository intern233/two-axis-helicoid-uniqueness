import TwoAxisHelicoid.HelicoidGroundStateMass
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace TwoAxisHelicoid

open Real MeasureTheory Set Filter Topology Metric
open scoped ContDiff

/-- The cutoff argument in Appendix D.3 for the actual ground state.
The error is the square of its inhomogeneous H¹ norm on the real
line. The same compact tests converge to the exact Jacobi energy. -/
theorem helicoidGroundState_compact_H1_approximation :
    ∃ ψ : ℕ → ℝ → ℝ, (∀ n, ContDiff ℝ ∞ (ψ n) ∧ HasCompactSupport (ψ n)) ∧
      Tendsto (fun n => ∫ x : ℝ, (ψ n x-helicoidGroundState x)^2+
        (deriv (ψ n) x-deriv helicoidGroundState x)^2) atTop (𝓝 0) ∧
      Tendsto (fun n => lineSchrodingerEnergy (fun x => 2*helicoidGroundState x^2) (ψ n))
        atTop (𝓝 (-2)) := by
  let f := helicoidGroundState
  let χ : ContDiffBump (0:ℝ) := default
  let R := fun n : ℕ => (n:ℝ)+1
  let cut := fun (n : ℕ) (x : ℝ) => χ (x/R n)
  let ψ := fun (n : ℕ) (x : ℝ) => cut n x*f x
  have bump : ContDiff ℝ ∞ (χ : ℝ → ℝ) := χ.contDiff
  have r1 (n : ℕ) : 1≤R n := by dsimp [R]; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have rp (n : ℕ) : 0<R n := lt_of_lt_of_le zero_lt_one (r1 n)
  have reg (n : ℕ) : ContDiff ℝ ∞ (cut n) ∧ HasCompactSupport (cut n) :=
    smooth_compact_dilate χ.contDiff χ.hasCompactSupport (rp n)
  have smooth (n : ℕ) : ContDiff ℝ ∞ (ψ n) ∧ HasCompactSupport (ψ n) :=
    ⟨(reg n).1.mul helicoidGroundState_smooth,(reg n).2.mul_right⟩
  have Dcut (n : ℕ) (x : ℝ) : deriv (cut n) x=deriv χ (x/R n)/R n := by
    simpa only [cut,Function.comp_def,id_eq,one_div,one_mul,div_eq_mul_inv] using
      (((bump.differentiable (by simp)) (x/R n)).hasDerivAt.comp x ((hasDerivAt_id x).div_const (R n))).deriv
  obtain ⟨C,bounded⟩ := χ.hasCompactSupport.deriv.exists_bound_of_continuous
    (bump.continuous_deriv (by simp))
  have C0 : 0≤C := (norm_nonneg _).trans (bounded 0)
  have dcut (n : ℕ) (x : ℝ) : |deriv (cut n) x|≤C := by
    rw [Dcut,abs_div,abs_of_pos (rp n)]
    apply (div_le_iff₀ (rp n)).mpr
    have bound : |deriv χ (x/R n)|≤C := bounded _
    nlinarith [mul_nonneg C0 (sub_nonneg.mpr (r1 n))]
  have cval (n : ℕ) (x : ℝ) : |cut n x|≤1 := by
    change |χ (x/R n)|≤1
    rw [abs_of_nonneg (χ.nonneg' _)]
    exact χ.le_one
  have val (n : ℕ) (x : ℝ) : |ψ n x|≤f x := by
    change |cut n x*f x|≤f x
    rw [abs_mul,abs_of_pos (helicoidGroundState_pos_le_one x).1]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (cval n x) (helicoidGroundState_pos_le_one x).1.le
  have dv (n : ℕ) (x : ℝ) : |deriv (ψ n) x|≤(C+1)*f x := by
    have eqn := deriv_fun_mul (((reg n).1.differentiable (by simp)) x)
      ((helicoidGroundState_smooth.differentiable (by simp)) x)
    change |deriv (fun y => cut n y*f y) x|≤_
    rw [eqn]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul,abs_mul,abs_of_pos (helicoidGroundState_pos_le_one x).1]
    have a := mul_le_mul_of_nonneg_right (dcut n x) (helicoidGroundState_pos_le_one x).1.le
    have b := mul_le_mul (cval n x) (helicoidGroundState_deriv_abs x) (abs_nonneg _) zero_le_one
    change |cut n x| * |deriv f x|≤1*f x at b
    linarith
  have eventually_exact (x : ℝ) : ∀ᶠ n : ℕ in atTop, ψ n x=f x ∧ deriv (ψ n) x=deriv f x := by
    obtain ⟨N,hN⟩ := exists_nat_gt |x|
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N:ℝ)≤(n:ℝ) := by exact_mod_cast hn
    have inside : x/R n∈ball (0:ℝ) χ.rIn := by
      rw [mem_ball,dist_zero_right,Real.norm_eq_abs,abs_div,abs_of_pos (rp n)]
      change |x|/R n<1
      apply (div_lt_one (rp n)).mpr
      dsimp [R]
      linarith
    have hχ := (χ.eventuallyEq_one_of_mem_ball inside).comp_tendsto (continuousAt_id.div_const (R n)).tendsto
    have germs : ψ n =ᶠ[𝓝 x] f := by
      filter_upwards [hχ] with y hy
      change χ (y/R n)=1 at hy
      change χ (y/R n)*f y=f y
      rw [hy,one_mul]
    exact ⟨germs.self_of_nhds,germs.deriv_eq⟩
  obtain ⟨mass,_,_,ground⟩ := helicoidGroundState_mass_and_energy
  have dominated (G : ℕ → ℝ → ℝ) (v : ℝ → ℝ) (K : ℝ) (meas : ∀ n, Continuous (G n))
      (bound : ∀ n x, |G n x|≤K*f x^2) (same : ∀ x, ∀ᶠ n : ℕ in atTop, G n x=v x) :
      Tendsto (fun n => ∫ x : ℝ, G n x) atTop (𝓝 (∫ x : ℝ, v x)) :=
    tendsto_integral_of_dominated_convergence (fun x => K*f x^2)
      (fun n => (meas n).aestronglyMeasurable) (mass.const_mul K)
      (fun n => ae_of_all _ (bound n))
      (ae_of_all _ fun x => tendsto_const_nhds.congr' ((same x).mono fun _ h => h.symm))
  have sqBound {a b : ℝ} (hb : 0≤b) (h : |a|≤b) : a^2≤b^2 := (sq_le_sq).mpr (by simpa only [abs_of_nonneg hb] using h)
  have subAbs (a b : ℝ) : |a-b|≤|a|+|b| := norm_sub_le a b
  have cp (n : ℕ) := (smooth n).1.continuous
  have cd (n : ℕ) := (smooth n).1.continuous_deriv (by simp)
  have cf : Continuous f := helicoidGroundState_smooth.continuous
  have df : Continuous (deriv f) := helicoidGroundState_smooth.continuous_deriv (by simp)
  refine ⟨ψ,smooth,?_,?_⟩
  · let G := fun (n : ℕ) (x : ℝ) => (ψ n x-f x)^2+(deriv (ψ n) x-deriv f x)^2
    have l := dominated G (fun _ => 0) (4+(C+2)^2)
      (fun n => (((cp n).sub cf).pow 2).add (((cd n).sub df).pow 2)) (by
        intro n x
        have hp := (helicoidGroundState_pos_le_one x).1.le
        have a := (subAbs (ψ n x) (f x)).trans (add_le_add (val n x) (abs_of_nonneg hp).le)
        have b := (subAbs (deriv (ψ n) x) (deriv f x)).trans (add_le_add (dv n x) (helicoidGroundState_deriv_abs x))
        have A := sqBound (show 0≤f x+f x by positivity) a
        have B := sqBound (show 0≤(C+1)*f x+f x by positivity) b
        dsimp [G]
        rw [abs_of_nonneg (by positivity)]
        nlinarith only [A,B]) (by
        intro x
        filter_upwards [eventually_exact x] with n h
        simp only [G,h.1,h.2,sub_self,zero_pow (by decide : 2≠0),add_zero])
    simpa only [integral_zero] using l
  · let G := fun (n : ℕ) (x : ℝ) => (deriv (ψ n) x)^2-2*f x^2*(ψ n x)^2
    have l := dominated G helicoidGroundEnergyDensity ((C+1)^2+2)
      (fun n => ((cd n).pow 2).sub ((continuous_const.mul (cf.pow 2)).mul ((cp n).pow 2))) (by
        intro n x
        have hx := helicoidGroundState_pos_le_one x
        have hf0 : 0≤f x := hx.1.le
        have A := sqBound (show 0≤(C+1)*f x by positivity) (dv n x)
        have B := sqBound zero_le_one ((val n x).trans hx.2)
        have P : 2*f x^2*(ψ n x)^2≤2*f x^2*1 := mul_le_mul_of_nonneg_left (B.trans_eq (one_pow _)) (by positivity)
        dsimp [G]
        have T := subAbs ((deriv (ψ n) x)^2) (2*f x^2*ψ n x^2)
        rw [abs_sq (deriv (ψ n) x),abs_of_nonneg (by positivity : 0≤2*f x^2*ψ n x^2)] at T
        nlinarith only [T,A,P]) (by
        intro x
        filter_upwards [eventually_exact x] with n h
        dsimp [G,helicoidGroundEnergyDensity]
        rw [h.1,h.2]
        change (deriv f x)^2-2*f x^2*f x^2=(deriv f x)^2-2*f x^4
        ring)
    rw [ground] at l
    exact l

/-- The original cutoff of sech gives a negative compact mode on the
line and, after dilation in the longitudinal variable, on the plane. -/
theorem helicoidGroundState_compact_cutoff_negative :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      lineSchrodingerEnergy (fun x => 2*helicoidGroundState x^2) ψ<0 := by
  obtain ⟨ψ,reg,_,lim⟩ := helicoidGroundState_compact_H1_approximation
  obtain ⟨n,hn⟩ := (lim.eventually_lt_const (by norm_num : (-2:ℝ)<0)).exists
  exact ⟨ψ n,(reg n).1,(reg n).2,hn⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.helicoidGroundState_compact_H1_approximation
#print axioms TwoAxisHelicoid.helicoidGroundState_compact_cutoff_negative
