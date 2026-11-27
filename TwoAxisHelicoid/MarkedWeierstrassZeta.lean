import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

noncomputable def markedZetaTerm (l z : ℂ) : ℂ := (z-l)⁻¹+l⁻¹+z/l^2

/-- The classical Weierstrass zeta function given by its convergent
lattice series, for an arbitrary marked complex lattice. -/
noncomputable def markedWeierstrassZeta (L : PeriodPair) (z : ℂ) : ℂ :=
  ∑' l : L.lattice, markedZetaTerm l z

private theorem marked_zeta_term_bound {r : ℝ} (hr : 0<r) {z l : ℂ} (small : ‖z‖<r)
    (far : 2*r≤‖l‖) : ‖markedZetaTerm l z‖≤2*r^2*‖l‖^(-3:ℝ) := by
  have positive : 0<‖l‖ := by linarith
  have reg : z-l≠0 := fun h => by rw [sub_eq_zero.mp h] at small; linarith
  have gap : ‖l‖/2≤‖z-l‖ := by rw [norm_sub_rev]; linarith [norm_sub_norm_le l z]
  have identity : markedZetaTerm l z=z^2/((z-l)*l^2) := by
    dsimp [markedZetaTerm]
    field_simp [reg,norm_pos_iff.mp positive]
    ring
  calc
    ‖markedZetaTerm l z‖=‖z‖^2/(‖z-l‖*‖l‖^2) := by rw [identity]; simp
    _ ≤ r^2/((‖l‖/2)*‖l‖^2) := by gcongr
    _ = 2*r^2/‖l‖^3 := by field_simp [positive.ne']
    _ = 2*r^2*‖l‖^(-3:ℝ) := by norm_cast

theorem marked_zeta_series_locally_uniform (L : PeriodPair) :
    HasSumLocallyUniformly (fun (l : L.lattice) z => markedZetaTerm l z) (markedWeierstrassZeta L) := by
  apply L.hasSumLocallyUniformly_aux (u:=fun r l => 2*r^2*‖l‖^(-3:ℝ))
  · intro r _
    exact (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _
  · intro r hr
    filter_upwards [eventually_ge_atTop (2*r)] with R hrR z hz l eq
    exact marked_zeta_term_bound hr hz (eq.symm ▸ hrR)

private theorem marked_zeta_term_derivative {l z : ℂ} (reg : z≠l) :
    HasDerivAt (markedZetaTerm l) (-(1/(z-l)^2-1/l^2)) z := by
  have h := ((((hasDerivAt_id' z).sub_const l).inv (sub_ne_zero.mpr reg)).add_const l⁻¹).add
    ((hasDerivAt_id' z).div_const (l^2))
  change HasDerivAt (markedZetaTerm l) (-1/(z-l)^2+1/l^2) z at h
  exact h.congr_deriv (by ring)

theorem marked_zeta_hasDerivAt (L : PeriodPair) {z : ℂ} (off : z∉L.lattice) :
    HasDerivAt (markedWeierstrassZeta L) (-L.weierstrassP z) z := by
  let U := (L.lattice:Set ℂ)ᶜ
  have op : IsOpen U := L.isClosed_lattice.isOpen_compl
  have d (i : L.lattice) {w : ℂ} (hw : w∈U) := marked_zeta_term_derivative (l:=(i:ℂ)) (z:=w)
    (fun e => hw (e ▸ i.property))
  have finite (s : Finset L.lattice) : DifferentiableOn ℂ (fun w => ∑ i∈s, markedZetaTerm i w) U :=
    .fun_sum fun i _ w hw => (d i hw).differentiableAt.differentiableWithinAt
  have series := marked_zeta_series_locally_uniform L
  have actual := series.hasSumLocallyUniformlyOn.differentiableOn (.of_forall finite) op
  have limits := series.tendstoLocallyUniformlyOn.deriv (.of_forall finite) op
  have target : Tendsto (fun s : Finset L.lattice => ∑ i∈s, -(1/(z-(i:ℂ))^2-1/(i:ℂ)^2)) atTop
      (𝓝 (-L.weierstrassP z)) := (L.hasSum_weierstrassP z).neg
  have same := target.congr (f₂:=fun s : Finset L.lattice => deriv (fun w => ∑ i∈s, markedZetaTerm i w) z)
    (fun s => (HasDerivAt.fun_sum (u:=s) (fun i _ => d i off)).deriv.symm)
  have eq := tendsto_nhds_unique (limits.tendsto_at off) same
  exact eq ▸ (actual.differentiableAt (op.mem_nhds off)).hasDerivAt

noncomputable def markedZetaIncrement (L : PeriodPair) (ω : ℂ) : ℂ :=
  markedWeierstrassZeta L (L.ω₁/2+ω)-markedWeierstrassZeta L (L.ω₁/2)

/-- The full period increment is independent of the starting point
anywhere in the lattice complement. -/
theorem marked_zeta_full_period (L : PeriodPair) {z ω : ℂ} (hz : z∉L.lattice) (hω : ω∈L.lattice) :
    markedWeierstrassZeta L (z+ω)-markedWeierstrassZeta L z=markedZetaIncrement L ω := by
  let D := fun w => markedWeierstrassZeta L (w+ω)-markedWeierstrassZeta L w
  have hd (w : ℂ) (hw : w∉L.lattice) : HasDerivAt D 0 w := by
    have reg : w+ω∉L.lattice := fun h => hw (by simpa only [add_sub_cancel_right] using L.lattice.sub_mem h hω)
    have h := ((marked_zeta_hasDerivAt L reg).comp w ((hasDerivAt_id' w).add_const ω)).sub (marked_zeta_hasDerivAt L hw)
    change HasDerivAt D ((-L.weierstrassP (w+ω))*1-(-L.weierstrassP w)) w at h
    exact h.congr_deriv (by rw [L.weierstrassP_add_coe w (⟨ω,hω⟩ : L.lattice)]; ring)
  have cnt : (L.lattice:Set ℂ).Countable := countable_of_Lindelof_of_discrete (X:=L.lattice)
  have conn := (cnt.isConnected_compl_of_one_lt_rank
    (by rw [← Module.finrank_eq_rank,Complex.finrank_real_complex]; norm_num : 1<Module.rank ℝ ℂ)).isPreconnected
  exact L.isClosed_lattice.isOpen_compl.is_const_of_deriv_eq_zero conn
    (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt) (fun w hw => (hd w hw).deriv) hz L.ω₁_div_two_notMem_lattice

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_zeta_series_locally_uniform
#print axioms TwoAxisHelicoid.marked_zeta_hasDerivAt
#print axioms TwoAxisHelicoid.marked_zeta_full_period
