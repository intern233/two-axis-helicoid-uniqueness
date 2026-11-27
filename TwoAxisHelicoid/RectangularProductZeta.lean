import TwoAxisHelicoid.RectangularProductQuasiperiod
import TwoAxisHelicoid.RectangularHalfPeriodReduction
import TwoAxisHelicoid.AlignedGaussLogGerm

namespace TwoAxisHelicoid
open Complex Set Filter Topology

private theorem periodic_derivative_off_lattice (L : PeriodPair) (J : ℂ → ℂ) {v c : ℂ}
    (hv : v∈L.lattice) (step : ∀ z∉L.lattice, J (z+v)=J z+c) :
    Function.Periodic (latticeRemovableExtension L (fun z => -deriv J z) 0) v := by
  classical
  intro z
  by_cases inside : z∈L.lattice
  · simp [latticeRemovableExtension,inside,L.lattice.add_mem inside hv]
  · have next : z+v∉L.lattice := fun h => inside (by simpa only [add_sub_cancel_right] using L.lattice.sub_mem h hv)
    have e : (fun w : ℂ => J (w+v))=ᶠ[𝓝 z] fun w => J w+c := by
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds inside] with w hw
      exact step w hw
    have d := e.deriv_eq
    rw [deriv_comp_add_const,deriv_add_const] at d
    simp only [latticeRemovableExtension,ite_eq_right next,ite_eq_right inside,d]

private theorem rectangular_log_one {t : ℝ} (ht : 0<t) :
    logDeriv (jacobiThetaProduct (rectangularProductNome t)) 1=0 := by
  have X : jacobiExp 1= -1 := by unfold jacobiExp; rw [mul_one,mul_comm,Complex.exp_pi_mul_I]
  have hp : ‖rectangularProductNome t‖*‖jacobiExp 1‖<1 := by simpa only [X,norm_neg,norm_one,mul_one] using rectangular_product_nome_norm ht
  have hm : ‖rectangularProductNome t‖*‖(jacobiExp 1)⁻¹‖<1 := by simpa only [X,inv_neg,inv_one,norm_neg,norm_one,mul_one] using rectangular_product_nome_norm ht
  rw [jacobiThetaProduct_logDeriv (rectangular_product_nome_norm ht) (by rw [X];norm_num) hp hm,X]
  norm_num

/-- The logarithmic derivative of the rectangular Jacobi product is
the actual lattice zeta series minus its linear normalization. The
double-pole classification fixes its derivative; periodicity and the
odd zeta values at the two real half periods fix both constants. -/
theorem rectangular_zeta_eq_product {t : ℝ} (ht : 0<t) {z : ℂ}
    (reg : z∉(manuscriptRectangularLattice t ht).lattice) :
    let R := manuscriptRectangularLattice t ht
    markedWeierstrassZeta R z=markedWeierstrassZeta R 1*z+
      logDeriv (jacobiThetaProduct (rectangularProductNome t)) z := by
  classical
  let R := manuscriptRectangularLattice t ht
  let F := jacobiThetaProduct (rectangularProductNome t)
  let J := logDeriv F
  let P := latticeRemovableExtension R (fun w => -deriv J w) 0
  have aF : Differentiable ℂ F := jacobiThetaProduct_differentiable (rectangular_product_nome_norm ht)
  have aJ {w : ℂ} (off : w∉R.lattice) : AnalyticAt ℂ J w :=
    (aF.analyticAt w).deriv.div (aF.analyticAt w) (rectangular_product_regular ht off)
  have value {w : ℂ} (off : w∉R.lattice) : P w= -deriv J w := by simp only [P,latticeRemovableExtension,ite_eq_right off]
  have localEq (w : ℂ) (off : w∉R.lattice) : P=ᶠ[𝓝 w] fun x => -deriv J x := by
    filter_upwards [R.isClosed_lattice.isOpen_compl.mem_nhds off] with x hx
    exact value hx
  have per₁ : Function.Periodic P R.ω₁ := periodic_derivative_off_lattice R J (c:=0) R.ω₁_mem_lattice
    (fun w _ => by change J (w+2)=J w+0;rw [add_zero];exact rectangular_product_log_period_two t w)
  have per₂ : Function.Periodic P R.ω₂ := periodic_derivative_off_lattice R J (c:= -(I*(Real.pi:ℂ))) R.ω₂_mem_lattice
    (fun w h => by simpa only [sub_eq_add_neg] using rectangular_product_log_period_imag ht h)
  have periodic (w v : ℂ) (hv : v∈R.lattice) : P (w+v)=P w := by
    obtain ⟨m,n,rfl⟩ := PeriodPair.mem_lattice.mp hv
    have h := per₁.zsmul m w
    have k := per₂.zsmul n (w+(m:ℂ)*R.ω₁)
    simp only [zsmul_eq_mul] at h k
    rw [← add_assoc,k,h]
  obtain ⟨r,ar,principal⟩ := simple_zero_log_derivative_principal_part (aF.analyticAt 0)
    (jacobiThetaProduct_zero _) (jacobiThetaProduct_deriv_zero_ne_zero (rectangular_product_nome_norm ht))
  have germ : J=ᶠ[𝓝[≠] (0:ℂ)] fun w => w⁻¹+r w := by
    filter_upwards [principal] with w h
    simpa only [J,logDeriv_apply,sub_zero] using h
  have remainder : ∀ᶠ w in 𝓝 (0:ℂ), w≠0 → P w=1/w^2+(-deriv r w) := by
    apply (eventually_nhdsWithin_iff (s:=({0}:Set ℂ)ᶜ)).mp
    filter_upwards [punctured_germ_eventually_local germ,self_mem_nhdsWithin,
      ar.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      mem_nhdsWithin_of_mem_nhds (R.compl_lattice_sdiff_singleton_mem_nhds (0:ℂ))] with w eq nz rwreg away
    have off : w∉R.lattice := fun h => away ⟨h,nz⟩
    have derivInv := (hasDerivAt_id' w).inv (show w≠0 from nz)
    have d : HasDerivAt (fun y : ℂ => y⁻¹+r y) (-1/w^2+deriv r w) w :=
      derivInv.add rwreg.differentiableAt.hasDerivAt
    rw [value off,eq.deriv_eq,d.deriv]
    ring
  have classify := elliptic_double_pole_classification R (1:ℂ) (f:=P)
    (fun w hw => ((aJ hw).deriv.differentiableAt.neg).congr_of_eventuallyEq (localEq w hw))
    periodic ar.deriv.neg remainder
  let B := -deriv r 0
  let Z := markedWeierstrassZeta R
  let D := fun w => Z w-J w-B*w
  have diff (w : ℂ) (hw : w∉R.lattice) : HasDerivAt D 0 w := by
    have d := ((marked_zeta_hasDerivAt R hw).sub (aJ hw).differentiableAt.hasDerivAt).sub ((hasDerivAt_id' w).const_mul B)
    have k := classify w hw
    rw [value hw,one_mul] at k
    change -deriv J w=R.weierstrassP w+B at k
    exact d.congr_deriv (by linear_combination k)
  have cnt : (R.lattice:Set ℂ).Countable := countable_of_Lindelof_of_discrete (X:=R.lattice)
  have conn := (cnt.isConnected_compl_of_one_lt_rank
    (by rw [← Module.finrank_eq_rank,Complex.finrank_real_complex]; norm_num : 1<Module.rank ℝ ℂ)).isPreconnected
  have same {x y : ℂ} (hx : x∉R.lattice) (hy : y∉R.lattice) : D x=D y :=
    R.isClosed_lattice.isOpen_compl.is_const_of_deriv_eq_zero conn
      (fun w hw => (diff w hw).differentiableAt.differentiableWithinAt) (fun w hw => (diff w hw).deriv) hx hy
  have one := (rectangular_semiperiod_nonmembers ht).1
  have neg : (-1:ℂ)∉R.lattice := by simpa using one
  have Jone : J 1=0 := rectangular_log_one ht
  have Jneg : J (-1)=0 := by
    have p := rectangular_product_log_period_two t (-1)
    change J (-1+2)=J (-1) at p
    norm_num only at p
    exact p.symm.trans Jone
  have endpoints := same one neg
  change Z 1-J 1-B*1=Z (-1)-J (-1)-B*(-1) at endpoints
  rw [show Z (-1)= -Z 1 from marked_zeta_odd R 1,Jone,Jneg] at endpoints
  have slope : B=Z 1 := by linear_combination -endpoints/2
  have atZ := same reg one
  change Z z-J z-B*z=Z 1-J 1-B*1 at atZ
  rw [Jone,slope] at atZ
  change Z z=Z 1*z+J z
  linear_combination atZ

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rectangular_zeta_eq_product

