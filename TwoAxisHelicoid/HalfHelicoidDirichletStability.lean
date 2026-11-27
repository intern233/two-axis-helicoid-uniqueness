import TwoAxisHelicoid.HalfHelicoidDirichletInterval
import TwoAxisHelicoid.PlanarEnergyStability

namespace TwoAxisHelicoid
open Set MeasureTheory Filter Topology
open scoped Topology ContDiff

/-- Dirichlet variations on the half helicoid. In conformal coordinates
(x,t), x is height and t is transverse distance in the parameter plane.
For any bounded strip the explicit gap is uniform over all test
functions, even when their supports approach the axis t=0. -/
theorem half_helicoid_rectangle_stability {R T : ℝ} (rp : 0<R) (tp : 0≤T)
    {v : ℝ × ℝ → ℝ} (smooth : ContDiff ℝ ∞ v)
    (sides : ∀ t∈Icc (0:ℝ) T, v (-R,t)=0 ∧ v (R,t)=0)
    (ends : ∀ x∈Icc (-R) R, v (x,0)=0 ∧ v (x,T)=0) :
    let K := Icc (-R) R ×ˢ Icc (0:ℝ) T
    (1/(R+1))^2*(∫ p in K, v p^2)≤∫ p in K,
      (fderiv ℝ v p (1,0))^2+(fderiv ℝ v p (0,1))^2-2*(Real.cosh p.2)⁻¹^2*v p^2 := by
  let I := Icc (-R) R
  let J := Icc (0:ℝ) T
  let K := I ×ˢ J
  let k := 1/(R+1)
  let A := fun p : ℝ × ℝ => (fderiv ℝ v p (1,0))^2-k^2*v p^2
  let B := fun p : ℝ × ℝ => (fderiv ℝ v p (0,1))^2-2*(Real.cosh p.2)⁻¹^2*v p^2
  let E := fun p : ℝ × ℝ => (fderiv ℝ v p (1,0))^2+(fderiv ℝ v p (0,1))^2-2*(Real.cosh p.2)⁻¹^2*v p^2
  have dv := smooth.differentiable (by simp)
  have cder (w : ℝ × ℝ) : Continuous (fun p => fderiv ℝ v p w) :=
    (smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have cA : Continuous A := (cder _ |>.pow 2).sub (continuous_const.mul (smooth.continuous.pow 2))
  have cB : Continuous B := by
    dsimp [B]; fun_prop (disch := intros; positivity)
  have cE : Continuous E := by
    dsimp [E]; fun_prop (disch := intros; positivity)
  have ck : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have ck' : IsCompact (J ×ˢ I) := isCompact_Icc.prod isCompact_Icc
  have order : -R≤R := by linarith
  have hA : 0≤∫ p in K, A p := by
    change 0≤∫ p in I ×ˢ J, A p ∂volume
    rw [Measure.volume_eq_prod,← setIntegral_prod_swap I J A,setIntegral_prod _ (by
      rw [← Measure.volume_eq_prod]; exact (cA.comp continuous_swap).continuousOn.integrableOn_compact ck')]
    apply setIntegral_nonneg measurableSet_Icc
    intro t ht
    have sf : ContDiff ℝ 1 (fun x => v (x,t)) := (smooth.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp)
    have gap := half_helicoid_axial_interval_gap rp sf (sides t ht).1 (sides t ht).2
    have slice (x : ℝ) : deriv (fun y => v (y,t)) x=fderiv ℝ v (x,t) (1,0) := planar_slice_deriv_x dv (x,t)
    simp_rw [slice] at gap
    simpa only [I,A,k,Prod.swap_prod_mk,integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le order] using gap
  have hB : 0≤∫ p in K, B p := by
    change 0≤∫ p in I ×ˢ J, B p ∂volume
    rw [Measure.volume_eq_prod,setIntegral_prod _ (by
      rw [← Measure.volume_eq_prod]; exact cB.continuousOn.integrableOn_compact ck)]
    apply setIntegral_nonneg measurableSet_Icc
    intro x hx
    have sf : ContDiff ℝ 1 (fun t => v (x,t)) := (smooth.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
    have energy := half_helicoid_transverse_interval_nonnegative tp sf (ends x hx).1 (ends x hx).2
    have slice (t : ℝ) : deriv (fun y => v (x,y)) t=fderiv ℝ v (x,t) (0,1) := planar_slice_deriv_y dv (x,t)
    simp_rw [slice] at energy
    simpa only [J,B,integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le tp] using energy
  have total := add_nonneg hA hB
  have identity : (fun p => A p+B p)=(fun p => E p-k^2*v p^2) := by
    funext p; dsimp [A,B,E]; ring
  rw [← integral_add (cA.continuousOn.integrableOn_compact ck) (cB.continuousOn.integrableOn_compact ck),
    identity,integral_sub (g:=fun p => k^2*v p^2) (cE.continuousOn.integrableOn_compact ck)
      ((continuous_const.mul (smooth.continuous.pow 2)).continuousOn.integrableOn_compact ck),integral_const_mul] at total
  exact sub_nonneg.mp total

/-- The gap also controls the mass in the induced Riemannian area
cosh²(t) dx dt. Consequently any bounded subdomain of a half helicoid
is strictly stable in the Dirichlet sense. Compactly supported tests
are viewed as smooth functions extended by zero outside their support. -/
theorem half_helicoid_compact_test_gap {R T : ℝ} (rp : 0<R) (tp : 0<T)
    {v : ℝ × ℝ → ℝ} (smooth : ContDiff ℝ ∞ v) (supp : tsupport v⊆Ioo (-R) R ×ˢ Ioo (0:ℝ) T) :
    ((1/(R+1))^2/(Real.cosh T)^2)*(∫ p : ℝ × ℝ, (Real.cosh p.2)^2*v p^2)≤
      planarQuadraticEnergy (fun p => 2*(Real.cosh p.2)⁻¹^2) v := by
  let K := Icc (-R) R ×ˢ Icc (0:ℝ) T
  let k := 1/(R+1)
  have incl : tsupport v⊆K := fun p hp => ⟨⟨(supp hp).1.1.le,(supp hp).1.2.le⟩,⟨(supp hp).2.1.le,(supp hp).2.2.le⟩⟩
  have vanish (p : ℝ × ℝ) (hop : p∉Ioo (-R) R ×ˢ Ioo (0:ℝ) T) : v p=0 :=
    Classical.byContradiction fun hp => hop (supp (subset_closure (show p∈Function.support v from hp)))
  have sides (t : ℝ) (_ : t∈Icc (0:ℝ) T) : v (-R,t)=0 ∧ v (R,t)=0 :=
    ⟨vanish _ (fun h => (lt_irrefl _ h.1.1)),vanish _ (fun h => (lt_irrefl _ h.1.2))⟩
  have ends (x : ℝ) (_ : x∈Icc (-R) R) : v (x,0)=0 ∧ v (x,T)=0 :=
    ⟨vanish _ (fun h => (lt_irrefl _ h.2.1)),vanish _ (fun h => (lt_irrefl _ h.2.2))⟩
  have rect := half_helicoid_rectangle_stability rp tp.le smooth sides ends
  let E := fun p : ℝ × ℝ => (fderiv ℝ v p (1,0))^2+(fderiv ℝ v p (0,1))^2-2*(Real.cosh p.2)⁻¹^2*v p^2
  have zeroAt {p : ℝ × ℝ} (outside : p∉K) : v p=0 ∧ fderiv ℝ v p=0 := by
    have hz := notMem_tsupport_iff_eventuallyEq.mp (fun mem => outside (incl mem) : p∉tsupport v)
    exact ⟨hz.self_of_nhds,by simpa only [fderiv_zero,Pi.zero_apply] using hz.fderiv_eq⟩
  have integralE : (∫ p in K, E p)=planarQuadraticEnergy (fun p => 2*(Real.cosh p.2)⁻¹^2) v := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    simp [E,(zeroAt hp).1,(zeroAt hp).2]
  let m := fun p : ℝ × ℝ => (Real.cosh p.2)^2*v p^2
  have integralM : (∫ p in K, m p)=∫ p, m p :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => by simp [m,(zeroAt hp).1]
  have ck : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have mass : (∫ p in K, m p)≤(Real.cosh T)^2*(∫ p in K, v p^2) := by
    have cm : Continuous m := ((Real.continuous_cosh.comp continuous_snd).pow 2).mul (smooth.continuous.pow 2)
    rw [← integral_const_mul]
    apply setIntegral_mono_on (cm.continuousOn.integrableOn_compact ck)
      ((continuous_const.mul (smooth.continuous.pow 2)).continuousOn.integrableOn_compact ck) ck.measurableSet
    intro p hp
    have mono : Real.cosh p.2≤Real.cosh T := Real.cosh_le_cosh.mpr (by
      rw [abs_of_nonneg hp.2.1,abs_of_nonneg tp.le]; exact hp.2.2)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.cosh_pos _).le mono 2) (sq_nonneg _)
  have hc := (sq_pos_of_pos (Real.cosh_pos T)).ne'
  change k^2*(∫ p in K, v p^2)≤∫ p in K, E p at rect
  rw [integralE] at rect
  change (k^2/(Real.cosh T)^2)*(∫ p, m p)≤_
  rw [← integralM]
  calc
    _ ≤ (k^2/(Real.cosh T)^2)*((Real.cosh T)^2*(∫ p in K, v p^2)) :=
      mul_le_mul_of_nonneg_left mass (by positivity)
    _ = k^2*(∫ p in K, v p^2) := by field_simp
    _ ≤ _ := rect

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.half_helicoid_rectangle_stability
#print axioms TwoAxisHelicoid.half_helicoid_compact_test_gap
