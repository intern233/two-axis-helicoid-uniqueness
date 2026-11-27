import TwoAxisHelicoid.RectangularSublatticeTrace
import TwoAxisHelicoid.MarkedWeierstrassZeta
import TwoAxisHelicoid.HalfThetaF
import TwoAxisHelicoid.SigmaAllIdentities

namespace TwoAxisHelicoid
open Complex Set Filter Topology

theorem marked_zeta_odd (L : PeriodPair) (z : ℂ) :
    markedWeierstrassZeta L (-z)= -markedWeierstrassZeta L z := by
  unfold markedWeierstrassZeta
  rw [← tsum_neg,← (Equiv.neg L.lattice).tsum_eq]
  apply tsum_congr
  intro l
  simp only [Equiv.neg_apply,NegMemClass.coe_neg,markedZetaTerm,neg_sub_neg,inv_neg,neg_sq,neg_div]
  rw [show (l:ℂ)-z= -(z-l) by ring,inv_neg]
  ring

theorem marked_zeta_full_first_increment (L : PeriodPair) :
    markedZetaIncrement L L.ω₁=2*markedWeierstrassZeta L (L.ω₁/2) := by
  have h := marked_zeta_full_period L (z:= -(L.ω₁/2)) (by simpa using L.ω₁_div_two_notMem_lattice) L.ω₁_mem_lattice
  rw [show -(L.ω₁/2)+L.ω₁=L.ω₁/2 by ring,marked_zeta_odd] at h
  linear_combination -h

/-- The rectangular reduction in Section 5, obtained by integrating the
index-two trace and evaluating its real full increment. Both zeta
functions here are fixed by the actual series or theta normalization. -/
theorem actual_rectangular_half_period_reduction {t : ℝ} (ht : 0<t) :
    let R := manuscriptRectangularLattice t ht
    let E := R.weierstrassP (1+I*t)
    let η := markedWeierstrassZeta R 1
    (rhombicPeriodPair t ht).weierstrassP 1= -2*E ∧
      thetaZeta t 1=2*η+E ∧ ellipticFReal t=(2*η-E).re := by
  let R := manuscriptRectangularLattice t ht
  let L := rhombicPeriodPair t ht
  let p : ℂ := 1+I*t
  let E := R.weierstrassP p
  let Z := markedWeierstrassZeta R
  let F := fun w => thetaZeta t w-Z w-Z (w-p)-E*w
  have diff (w : ℂ) (hw : w∉L.lattice) : HasDerivAt F 0 w := by
    have regular := (rectangular_lattice_and_coset ht w).not.mp hw
    have dw := (marked_zeta_hasDerivAt R (z:=w-p) (fun h => regular (Or.inr h))).comp w ((hasDerivAt_id' w).sub_const p)
    have d := (((thetaZeta_hasDerivAt_of_pos ht ht hw).sub (marked_zeta_hasDerivAt R (z:=w) (fun h => regular (Or.inl h)))).sub dw).sub
      ((hasDerivAt_id' w).const_mul E)
    have trace := rhombic_weierstrass_rectangular_trace ht hw
    change L.weierstrassP w=R.weierstrassP w+R.weierstrassP (w-p)-E at trace
    change HasDerivAt F (-L.weierstrassP w-(-R.weierstrassP w)-(-R.weierstrassP (w-p))*1-E*1) w at d
    exact d.congr_deriv (by linear_combination -trace)
  have cnt : (L.lattice:Set ℂ).Countable := countable_of_Lindelof_of_discrete (X:=L.lattice)
  have conn := (cnt.isConnected_compl_of_one_lt_rank
    (by rw [← Module.finrank_eq_rank,Complex.finrank_real_complex]; norm_num : 1<Module.rank ℝ ℂ)).isPreconnected
  have off : (1:ℂ)∉L.lattice := by convert L.ω₁_div_two_notMem_lattice using 1; norm_num [L,rhombicPeriodPair]
  have negOff : (-1:ℂ)∉L.lattice := by simpa using off
  have law := L.isClosed_lattice.isOpen_compl.is_const_of_deriv_eq_zero conn
    (fun w hw => (diff w hw).differentiableAt.differentiableWithinAt) (fun w hw => (diff w hw).deriv) off negOff
  have reg : (-1:ℂ)-p∉R.lattice := fun h => negOff ((rectangular_lattice_and_coset ht _).mpr (Or.inr h))
  have step := marked_zeta_full_period R reg R.ω₁_mem_lattice
  rw [marked_zeta_full_first_increment] at step
  change Z (-1-p+2)-Z (-1-p)=2*Z ((2:ℂ)/2) at step
  rw [show (-1:ℂ)-p+2=1-p by ring,show (2:ℂ)/2=1 by norm_num] at step
  have odd : Z (-1)= -Z 1 := marked_zeta_odd R 1
  change F 1=F (-1) at law
  dsimp only [F] at law
  rw [thetaZeta_neg,odd] at law
  have eta : thetaZeta t 1=2*Z 1+E := by linear_combination (law+step)/2
  have val := rhombic_real_half_value_rectangular ht
  change L.weierstrassP 1= -2*E at val
  refine ⟨val,eta,?_⟩
  rw [← ellipticF_eq_ellipticFReal ht]
  change (thetaEtaExpression t+L.weierstrassP 1).re=(2*Z 1-E).re
  rw [← thetaZeta_one,eta,val]
  congr 1
  ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_zeta_full_first_increment
#print axioms TwoAxisHelicoid.actual_rectangular_half_period_reduction
