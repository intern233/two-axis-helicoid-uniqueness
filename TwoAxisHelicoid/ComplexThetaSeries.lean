import TwoAxisHelicoid.ThetaHeat
import Mathlib.Analysis.Normed.Group.FunctionSeries

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

noncomputable def complexThetaTerm (t : ℂ) (j n : ℕ) (v : ℂ) : ℂ :=
  thetaSign n*Complex.exp (-Real.pi*t*n*(n+1)/2)*(2*n+1:ℂ)^j*sineJet j ((2*n+1:ℂ)*v)

noncomputable def complexThetaJet (t : ℂ) (j : ℕ) (v : ℂ) : ℂ :=
  ∑' n, complexThetaTerm t j n v

theorem complexThetaTerm_ofReal (t : ℝ) (j n : ℕ) (v : ℂ) :
    complexThetaTerm t j n v = thetaTerm t j n v := by
  unfold complexThetaTerm thetaTerm
  rw [Complex.ofReal_exp]
  push_cast
  rfl

theorem complexThetaJet_ofReal (t : ℝ) (j : ℕ) (v : ℂ) :
    complexThetaJet t j v = thetaJet t j v := by
  simp only [complexThetaJet,thetaJet,complexThetaTerm_ofReal]

theorem complexThetaTerm_norm (t : ℂ) (j n : ℕ) (v : ℂ) :
    ‖complexThetaTerm t j n v‖ = ‖thetaTerm t.re j n v‖ := by
  simp only [complexThetaTerm,thetaTerm,norm_mul,Complex.norm_exp,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (Real.exp_nonneg _)]
  congr 2
  congr 1
  simp [Complex.mul_re,Complex.mul_im]

theorem complexThetaTerm_norm_le {t : ℂ} {tlo y : ℝ} (ht : tlo ≤ t.re) {v : ℂ}
    (hv : |v.im| ≤ y) (j n : ℕ) : ‖complexThetaTerm t j n v‖ ≤ thetaMajorant tlo y j n := by
  rw [complexThetaTerm_norm]
  exact thetaTerm_norm_le ht hv j n

theorem complexThetaTerm_summable {t : ℂ} (ht : 0 < t.re) (j : ℕ) (v : ℂ) :
    Summable (fun n => complexThetaTerm t j n v) :=
  (thetaMajorant_summable ht |v.im| j).of_norm_bounded
    (fun n => complexThetaTerm_norm_le le_rfl le_rfl j n)

theorem complexThetaTerm_space_hasDerivAt (t : ℂ) (j n : ℕ) (v : ℂ) :
    HasDerivAt (complexThetaTerm t j n) (complexThetaTerm t (j+1) n v) v := by
  have harg := (hasDerivAt_id v).const_mul (2*n+1:ℂ)
  have hd := ((hasDerivAt_sineJet j _).comp v harg).const_mul
    (thetaSign n*Complex.exp (-Real.pi*t*n*(n+1)/2)*(2*n+1:ℂ)^j)
  convert hd using 1
  · rfl
  · simp only [complexThetaTerm,pow_succ,id_eq]
    ring

theorem complexThetaTerm_add_two (t : ℂ) (j n : ℕ) (v : ℂ) :
    complexThetaTerm t (j+2) n v = -(2*n+1:ℂ)^2*complexThetaTerm t j n v := by
  simp only [complexThetaTerm,pow_add,sineJet_add_two]
  ring

theorem complexThetaTerm_time_hasDerivAt (t : ℂ) (j n : ℕ) (v : ℂ) :
    HasDerivAt (fun s : ℂ => complexThetaTerm s j n v)
      ((Real.pi/8:ℂ)*(complexThetaTerm t (j+2) n v+complexThetaTerm t j n v)) t := by
  have ha := ((((hasDerivAt_id t).const_mul (-Real.pi:ℂ)).mul_const (n:ℂ)).mul_const
    (n+1)).div_const 2
  have hd := (((ha.cexp).const_mul (thetaSign n)).mul_const ((2*n+1:ℂ)^j)).mul_const
    (sineJet j ((2*n+1:ℂ)*v))
  convert hd using 1
  · rfl
  · rw [complexThetaTerm_add_two]
    simp only [complexThetaTerm,id_eq]
    ring

theorem complexThetaJet_space_hasDerivAt {t : ℂ} (ht : 0 < t.re) (j : ℕ) (v : ℂ) :
    HasDerivAt (complexThetaJet t j) (complexThetaJet t (j+1) v) v := by
  let U : Set ℂ := {w | |w.im| < |v.im|+1}
  have hU : IsOpen U := isOpen_lt Complex.continuous_im.abs continuous_const
  have hv : v ∈ U := by dsimp [U]; linarith
  have hu := thetaMajorant_summable ht (|v.im|+1) j
  have hf : ∀ n, DifferentiableOn ℂ (complexThetaTerm t j n) U :=
    fun n w _ => (complexThetaTerm_space_hasDerivAt t j n w).differentiableAt.differentiableWithinAt
  have hb : ∀ n w, w ∈ U → ‖complexThetaTerm t j n w‖ ≤ thetaMajorant t.re (|v.im|+1) j n :=
    fun n w hw => complexThetaTerm_norm_le le_rfl hw.le j n
  have hd := Complex.differentiableOn_tsum_of_summable_norm hu hf hU hb
  have hs := Complex.hasSum_deriv_of_summable_norm hu hf hU hb hv
  have heq : deriv (complexThetaJet t j) v = complexThetaJet t (j+1) v := by
    have hterms : (fun n => deriv (complexThetaTerm t j n) v) =
        (fun n => complexThetaTerm t (j+1) n v) :=
      funext (fun n => (complexThetaTerm_space_hasDerivAt t j n v).deriv)
    rw [hterms] at hs
    exact hs.tsum_eq.symm
  rw [← heq]
  exact (hd.differentiableAt (hU.mem_nhds hv)).hasDerivAt

theorem complexThetaJet_time_hasDerivAt {t : ℂ} (ht : 0 < t.re) (j : ℕ) (v : ℂ) :
    HasDerivAt (fun s : ℂ => complexThetaJet s j v)
      ((Real.pi/8:ℂ)*(complexThetaJet t (j+2) v+complexThetaJet t j v)) t := by
  let U : Set ℂ := {w | t.re/2 < w.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have htU : t ∈ U := by dsimp [U]; linarith
  have hu := thetaMajorant_summable (show 0 < t.re/2 by positivity) |v.im| j
  have hf : ∀ n, DifferentiableOn ℂ (fun s => complexThetaTerm s j n v) U :=
    fun n s _ => (complexThetaTerm_time_hasDerivAt s j n v).differentiableAt.differentiableWithinAt
  have hb : ∀ n s, s ∈ U → ‖complexThetaTerm s j n v‖ ≤ thetaMajorant (t.re/2) |v.im| j n :=
    fun n s hs => complexThetaTerm_norm_le hs.le le_rfl j n
  have hd := Complex.differentiableOn_tsum_of_summable_norm hu hf hU hb
  have hs := Complex.hasSum_deriv_of_summable_norm hu hf hU hb htU
  have hterms : (fun n => deriv (fun s => complexThetaTerm s j n v) t) =
      (fun n => (Real.pi/8:ℂ)*(complexThetaTerm t (j+2) n v+complexThetaTerm t j n v)) :=
    funext (fun n => (complexThetaTerm_time_hasDerivAt t j n v).deriv)
  rw [hterms] at hs
  have heq := hs.tsum_eq
  rw [tsum_mul_left,Summable.tsum_add (complexThetaTerm_summable ht (j+2) v)
    (complexThetaTerm_summable ht j v)] at heq
  unfold complexThetaJet
  rw [heq]
  exact (hd.differentiableAt (hU.mem_nhds htU)).hasDerivAt

theorem complexThetaJet_joint_continuousOn {tlo y : ℝ} (htlo : 0 < tlo) (j : ℕ) :
    ContinuousOn (fun p : ℂ × ℂ => complexThetaJet p.1 j p.2)
      {p | tlo ≤ p.1.re ∧ |p.2.im| ≤ y} := by
  unfold complexThetaJet
  apply continuousOn_tsum
    (fun n => (show Continuous (fun p : ℂ × ℂ => complexThetaTerm p.1 j n p.2) by
      unfold complexThetaTerm sineJet
      fun_prop).continuousOn) (thetaMajorant_summable htlo y j)
  intro n p hp
  exact complexThetaTerm_norm_le hp.1 hp.2 j n

theorem complexThetaJet_joint_continuousAt {t : ℂ} (ht : 0 < t.re) (j : ℕ) (v : ℂ) :
    ContinuousAt (fun p : ℂ × ℂ => complexThetaJet p.1 j p.2) (t,v) := by
  have h1 : ∀ᶠ p : ℂ × ℂ in 𝓝 (t,v), t.re/2 < p.1.re :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds (by dsimp; linarith)
  have h2 : ∀ᶠ p : ℂ × ℂ in 𝓝 (t,v), |p.2.im| < |v.im|+1 :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by dsimp; linarith)
  exact (complexThetaJet_joint_continuousOn (y := |v.im|+1) (show 0 < t.re/2 by positivity) j).continuousAt
    (Filter.mem_of_superset (h1.and h2) (fun _ h => ⟨h.1.le,h.2.le⟩))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.complexThetaJet_time_hasDerivAt
