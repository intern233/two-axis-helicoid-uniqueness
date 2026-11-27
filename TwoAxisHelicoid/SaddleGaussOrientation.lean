import TwoAxisHelicoid.GaussRealCoefficients
import TwoAxisHelicoid.SigmaRealPositive
import TwoAxisHelicoid.CentralHeightArc

namespace TwoAxisHelicoid
open Complex Set Filter Metric
open scoped ComplexConjugate Topology
attribute [local irreducible] thetaSigma thetaZeta

/-- At the positive saddle the Gauss map has a simple zero with a
strictly positive imaginary derivative in the normalized coordinate. -/
theorem saddle_gauss_first_jet {t a : ℝ} (lower : 43/50≤t) (ha : a∈Ioo (0:ℝ) 1) :
    AnalyticAt ℂ (thetaGauss t a 1) (a:ℂ) ∧ thetaGauss t a 1 (a:ℂ)=0 ∧
      ∃ k : ℝ, 0<k ∧ HasDerivAt (thetaGauss t a 1) (I*(k:ℂ)) (a:ℂ) := by
  have ht : 0<t := by linarith
  have off := real_not_mem_rhombic_lattice_of_pos ht ha.1 (ha.2.trans (by norm_num))
  let E := fun z : ℂ => 2*((a:ℂ)-1)*thetaZeta t z+2*thetaEtaExpression t*z
  let A := fun z : ℂ => I*exp (E z)/thetaSigma t (z+a)
  let S := fun z : ℂ => thetaSigma t (z-a)
  have eq : thetaGauss t a 1=fun z => A z*S z := by
    funext z
    simp only [thetaGauss,Int.cast_one,mul_one,E,A,S]
    ring
  have eA : AnalyticAt ℂ E (a:ℂ) := ((analyticAt_const.mul (thetaZeta_analyticAt_of_pos ht off)).add (analyticAt_const.mul analyticAt_id))
  have sp := thetaSigma_re_pos lower (x:=a+a) (by linarith [ha.1]) (by linarith [ha.2])
  have sig : thetaSigma t ((a:ℂ)+a)=((thetaSigma t ((a+a:ℝ):ℂ)).re:ℂ) := by
    rw [← ofReal_add]
    apply Complex.ext
    · rfl
    · exact thetaSigma_real _ _
  have den : thetaSigma t ((a:ℂ)+a)≠0 := by rw [sig]; exact ofReal_ne_zero.mpr sp.ne'
  have aa : AnalyticAt ℂ A (a:ℂ) := (analyticAt_const.mul eA.cexp).div
    ((thetaSigma_analyticAt ht _).comp (f:=fun z : ℂ => z+a) (analyticAt_id.add analyticAt_const)) den
  have j : HasDerivAt S 1 (a:ℂ) := by
    have h := (thetaSigma_hasDerivAt_zero_of_pos ht).comp_of_eq (x:=(a:ℂ)) ((hasDerivAt_id (a:ℂ)).sub_const (a:ℂ)) (by simp)
    change HasDerivAt S (1*(1:ℂ)) (a:ℂ) at h
    rwa [one_mul] at h
  have asig : AnalyticAt ℂ S (a:ℂ) := (thetaSigma_analyticAt ht _).comp (analyticAt_id.sub analyticAt_const)
  have z : S (a:ℂ)=0 := by simp [S,thetaSigma_zero]
  have ere : E (a:ℂ)=((E (a:ℂ)).re:ℂ) := by
    apply Complex.ext
    · rfl
    · simp [E,mul_im,thetaZeta_real,thetaEtaExpression_real]
  let k := Real.exp (E (a:ℂ)).re/(thetaSigma t ((a+a:ℝ):ℂ)).re
  have val : A (a:ℂ)=I*(k:ℂ) := by
    dsimp only [A,k]
    have ee : exp (E (a:ℂ))=(Real.exp (E (a:ℂ)).re:ℂ) := (congrArg exp ere).trans (ofReal_exp _).symm
    rw [ee,sig,ofReal_div]
    ring
  rw [eq]
  refine ⟨aa.mul asig,by change A (a:ℂ)*S (a:ℂ)=0; rw [z,mul_zero],k,div_pos (Real.exp_pos _) sp,?_⟩
  have res := aa.differentiableAt.hasDerivAt.mul j
  change HasDerivAt (fun v => A v*S v) (deriv A (a:ℂ)*S (a:ℂ)+A (a:ℂ)*1) (a:ℂ) at res
  rwa [z,mul_zero,zero_add,mul_one,val] at res

/-- The real part of the Gauss map is negative throughout a one-sided
neighborhood above the entire short real segment around the saddle. -/
theorem saddle_upper_gauss_real_negative {t a : ℝ} (lower : 43/50≤t) (ha : a∈Ioo (0:ℝ) 1) :
    ∃ ε : ℝ, 0<ε ∧ ∀ x y : ℝ, |x-a|<ε → y∈Ioo (0:ℝ) ε → (thetaGauss t a 1 ((x:ℂ)+I*y)).re<0 := by
  let G := thetaGauss t a 1
  obtain ⟨aa,_,k,kp,jet⟩ := saddle_gauss_first_jet lower ha
  have atp : 0<(deriv G (a:ℂ)).im := by rw [jet.deriv]; simpa only [I_mul_im,ofReal_re] using kp
  have cs := continuous_im.continuousAt.comp aa.deriv.continuousAt
  obtain ⟨δ,dp,box⟩ := Metric.mem_nhds_iff.mp (show {z : ℂ | AnalyticAt ℂ G z ∧ 0<(deriv G z).im}∈𝓝 (a:ℂ) from by
    filter_upwards [aa.eventually_analyticAt,cs.eventually (Ioi_mem_nhds atp)] with u h e using ⟨h,e⟩)
  refine ⟨δ/3,by linarith,?_⟩
  intro x y hx hy
  let Z := fun v : ℝ => (x:ℂ)+I*v
  have reg (v : ℝ) (hv : v∈Icc 0 y) : AnalyticAt ℂ G (Z v) ∧ 0<(deriv G (Z v)).im := box (by
    rw [mem_ball,dist_eq_norm,show Z v-a=((x-a:ℝ):ℂ)+I*v by dsimp [Z]; push_cast; ring]
    have b := norm_add_le ((x-a:ℝ):ℂ) (I*(v:ℂ))
    rw [norm_mul,norm_I,one_mul,norm_real,Real.norm_eq_abs,norm_real,Real.norm_eq_abs,abs_of_nonneg hv.1] at b
    linarith [hy.2,hv.2])
  have line (v : ℝ) : HasDerivAt Z I v := by simpa [Z] using ((hasDerivAt_id v).ofReal_comp.const_mul I).const_add (x:ℂ)
  have der (v : ℝ) (hv : v∈Icc 0 y) : HasDerivAt (fun u => (G (Z u)).re) (-(deriv G (Z v)).im) v := by
    have h := reCLM.hasFDerivAt.comp_hasDerivAt v ((reg v hv).1.differentiableAt.hasDerivAt.scomp v (line v))
    change HasDerivAt (fun u => (G (Z u)).re) (I*deriv G (Z v)).re v at h
    rwa [I_mul_re] at h
  have dec := strictAntiOn_of_deriv_neg (convex_Icc 0 y) (fun v hv => (der v hv).continuousAt.continuousWithinAt)
    (fun v hv => (der v (interior_subset hv)).deriv.trans_lt (neg_lt_zero.mpr (reg _ (interior_subset hv)).2))
  have val := dec (left_mem_Icc.mpr hy.1.le) (right_mem_Icc.mpr hy.1.le) hy.1
  have zero := congrArg re (thetaGauss_conj t a 1 (x:ℂ))
  simp only [conj_ofReal,neg_re,conj_re] at zero
  have ze : (G (Z 0)).re=0 := by simp only [Z,ofReal_zero,mul_zero,add_zero,G]; linarith
  exact val.trans_eq ze

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.saddle_gauss_first_jet
#print axioms TwoAxisHelicoid.saddle_upper_gauss_real_negative
