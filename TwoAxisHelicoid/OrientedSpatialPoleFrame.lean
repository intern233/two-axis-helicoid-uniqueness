import TwoAxisHelicoid.OrthogonalMeanCurvature
import TwoAxisHelicoid.ChartSecondFundamentalWeingarten
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace TwoAxisHelicoid
open Matrix Complex Set Filter Topology
open scoped Matrix Topology RealInnerProductSpace

/-- Rotate any specified oriented, orthonormal tangent pair into the
horizontal plane. The last coordinate is its actual signed normal
component, and oriented cross products are preserved. -/
theorem oriented_frame_with_last_normal (A B : Fin 3 → ℝ)
    (aa : A ⬝ᵥ A=1) (bb : B ⬝ᵥ B=1) (ab : A ⬝ᵥ B=0) :
    ∃ T : (Fin 3 → ℝ) ≃L[ℝ] (Fin 3 → ℝ), (∀ u v, T u ⬝ᵥ T v=u ⬝ᵥ v) ∧
      (∀ u v, T u ⨯₃ T v=T (u ⨯₃ v)) ∧ ∀ v, T v 2=(A ⨯₃ B) ⬝ᵥ v := by
  let N := A ⨯₃ B
  have ba : B ⬝ᵥ A=0 := (dotProduct_comm _ _).trans ab
  have an : A ⬝ᵥ N=0 := dot_self_cross _ _
  have bn : B ⬝ᵥ N=0 := dot_cross_self _ _
  have na : N ⬝ᵥ A=0 := (dotProduct_comm _ _).trans an
  have nb : N ⬝ᵥ B=0 := (dotProduct_comm _ _).trans bn
  have nn : N ⬝ᵥ N=1 := by
    change (A ⨯₃ B) ⬝ᵥ (A ⨯₃ B)=1
    rw [cross_dot_cross,aa,bb,ab]
    ring
  let U : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
    (ContinuousLinearMap.proj (0:Fin 3)).smulRight A+(ContinuousLinearMap.proj (1:Fin 3)).smulRight B+
      (ContinuousLinearMap.proj (2:Fin 3)).smulRight N
  have form (v : Fin 3 → ℝ) : U v=v 0 • A+v 1 • B+v 2 • N := rfl
  have iso (v w : Fin 3 → ℝ) : U v ⬝ᵥ U w=v ⬝ᵥ w := by
    rw [form,form]
    simp only [add_dotProduct,dotProduct_add,smul_dotProduct,dotProduct_smul,smul_eq_mul,
      aa,bb,ab,ba,an,bn,na,nb,nn,mul_zero,mul_one,zero_add,add_zero]
    simp [dotProduct,Fin.sum_univ_succ]
    ring
  have inj : Function.Injective U := by
    intro v w eqn
    have zero := iso (v-w) (v-w)
    rw [map_sub,eqn,sub_self,zero_dotProduct] at zero
    exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp zero.symm)
  let e := (LinearEquiv.ofBijective U.toLinearMap ⟨inj,LinearMap.injective_iff_surjective.mp inj⟩).toContinuousLinearEquiv
  have inverse (v : Fin 3 → ℝ) : U (e.symm v)=v := e.apply_symm_apply _
  have det : (LinearMap.toMatrix' U.toLinearMap).det=1 := by
    have h := spatial_triple_product_map U.toLinearMap ![0,0,1] ![1,0,0] ![0,1,0]
    change U _ ⬝ᵥ (U _ ⨯₃ U _)=_ at h
    have e1 : U ![1,0,0]=A := by rw [form]; simp
    have e2 : U ![0,1,0]=B := by rw [form]; simp
    have e3 : U ![0,0,1]=N := by rw [form]; simp
    rw [e1,e2,e3] at h
    have ij : (![1,0,0] : Fin 3 → ℝ) ⨯₃ ![0,1,0]=![0,0,1] := by
      ext j; fin_cases j <;> norm_num [cross_apply]
    rw [ij] at h
    simpa [dotProduct,Fin.sum_univ_succ] using
      (h.symm.trans (show N ⬝ᵥ (A ⨯₃ B)=1 from nn))
  have crossU (v w : Fin 3 → ℝ) : U v ⨯₃ U w=U (v ⨯₃ w) := by
    let δ := U v ⨯₃ U w-U (v ⨯₃ w)
    have t := spatial_triple_product_map U.toLinearMap (e.symm δ) v w
    change U (e.symm δ) ⬝ᵥ (U v ⨯₃ U w)=_ at t
    rw [det,mul_one,← iso (e.symm δ) (v ⨯₃ w),inverse] at t
    apply sub_eq_zero.mp
    apply dotProduct_self_eq_zero.mp
    change δ ⬝ᵥ (U v ⨯₃ U w-U (v ⨯₃ w))=0
    rw [dotProduct_sub,t,sub_self]
  refine ⟨e.symm,fun v w => (iso (e.symm v) (e.symm w)).symm.trans (by rw [inverse,inverse]),?_,?_⟩
  · intro v w
    apply inj
    rw [← crossU,inverse,inverse,inverse]
  · intro v
    have h := iso ![0,0,1] (e.symm v)
    rw [inverse,form] at h
    simpa [dotProduct,Fin.sum_univ_succ] using h.symm

theorem oriented_spatial_frame_normal {T : (Fin 3 → ℝ) ≃L[ℝ] (Fin 3 → ℝ)}
    (ortho : ∀ v w, T v ⬝ᵥ T w=v ⬝ᵥ w) (cross : ∀ v w,T v ⨯₃ T w=T (v ⨯₃ w))
    (Y : ℂ → Fin 3 → ℝ) (z : ℂ) :
    unitCrossNormal (fderiv ℝ (T ∘ Y) z 1) (fderiv ℝ (T ∘ Y) z I)=
      T (unitCrossNormal (fderiv ℝ Y z 1) (fderiv ℝ Y z I)) := by
  rw [T.comp_fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,unitCrossNormal,cross,ortho,map_smul]

theorem euclidean_speed_of_orthogonal_frame {T : (Fin 3 → ℝ) ≃L[ℝ] (Fin 3 → ℝ)}
    (ortho : ∀ v w, T v ⬝ᵥ T w=v ⬝ᵥ w) (v : Fin 3 → ℝ) :
    ‖coordinateToEuclidean (T v)‖=‖coordinateToEuclidean v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [← real_inner_self_eq_norm_sq,coordinateToEuclidean_apply,EuclideanSpace.inner_toLp_toLp,star_trivial] using ortho v v

/-- Spatial speed and the Euclidean norm of the derivative of the
actual unit normal are invariant under an oriented orthogonal change
of physical coordinates. -/
theorem oriented_spatial_frame_derivative_lengths {T : (Fin 3 → ℝ) ≃L[ℝ] (Fin 3 → ℝ)}
    (ortho : ∀ v w, T v ⬝ᵥ T w=v ⬝ᵥ w) (cross : ∀ v w,T v ⨯₃ T w=T (v ⨯₃ w))
    (Y : ℂ → Fin 3 → ℝ) (z v : ℂ) :
    ‖fderiv ℝ (euclideanUnitChartNormal (T ∘ Y)) z v‖=‖fderiv ℝ (euclideanUnitChartNormal Y) z v‖ ∧
      ‖coordinateToEuclidean (fderiv ℝ (T ∘ Y) z v)‖=‖coordinateToEuclidean (fderiv ℝ Y z v)‖ := by
  let R := surfaceCartesianEquiv.trans (T.trans surfaceCartesianEquiv.symm)
  have rotate (w : Fin 3 → ℝ) : R (coordinateToEuclidean w)=coordinateToEuclidean (T w) := by
    change coordinateToEuclidean (T (surfaceCartesianEquiv (coordinateToEuclidean w)))=_
    rw [surfaceCartesian_toEuclidean]
  have same : euclideanUnitChartNormal (T ∘ Y)=R ∘ euclideanUnitChartNormal Y := by
    funext p
    rw [Function.comp_apply,euclidean_chart_normal_eq_unitCross,euclidean_chart_normal_eq_unitCross,
      oriented_spatial_frame_normal ortho cross,rotate]
  constructor
  · rw [same,R.comp_fderiv]
    let W := fderiv ℝ (euclideanUnitChartNormal Y) z v
    change ‖R W‖=‖W‖
    obtain ⟨w,hw⟩ : ∃ w, coordinateToEuclidean w=W := ⟨_,surfaceEuclidean_toCartesian W⟩
    rw [← hw,rotate,euclidean_speed_of_orthogonal_frame ortho]
  · rw [T.comp_fderiv]
    exact euclidean_speed_of_orthogonal_frame ortho _

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.oriented_frame_with_last_normal
#print axioms TwoAxisHelicoid.oriented_spatial_frame_derivative_lengths
