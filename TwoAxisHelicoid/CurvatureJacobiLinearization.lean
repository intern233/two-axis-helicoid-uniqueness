import TwoAxisHelicoid.NormalVelocityLaplacian
import TwoAxisHelicoid.MeanCurvatureNumerator

namespace TwoAxisHelicoid
open Complex Matrix Filter InnerProductSpace Laplacian
open scoped Topology ContDiff

private abbrev V3 := Fin 3 → ℝ

private noncomputable def meanJet (A B C D E : V3) : ℝ :=
  meanCurvatureNumerator A B C D E /
    (2*Real.sqrt ((A ⨯₃ B) ⬝ᵥ (A ⨯₃ B))*((A ⬝ᵥ A)*(B ⬝ᵥ B)-(A ⬝ᵥ B)^2))

private theorem coordinate_mean_eq_jet (X : ℂ → V3) (z : ℂ) :
    coordinateMeanCurvature X z =
      meanJet (fderiv ℝ X z 1) (fderiv ℝ X z I)
        (fderiv ℝ (fderiv ℝ X) z 1 1) (fderiv ℝ (fderiv ℝ X) z 1 I)
        (fderiv ℝ (fderiv ℝ X) z I I) := by
  simp only [coordinateMeanCurvature,unitCrossNormal,iteratedFDeriv_two_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,dotProduct_smul,smul_eq_mul,
    meanJet,meanCurvatureNumerator,div_eq_mul_inv,_root_.mul_inv_rev]
  ring

/-- Differentiate the mean curvature at a harmonic conformal two-jet.
The varied jets may have arbitrary metric and mixed coefficients. -/
private theorem meanJet_derivative
    {A B C D E : ℝ → V3} {U V P Q R n nx ny : V3} {g b c : ℝ}
    (frame : ConformalNormalFrame (A 0) (B 0) n nx ny g b c)
    (cross0 : A 0 ⨯₃ B 0 = g • n)
    (trace0 : E 0 = -C 0) (curvX : C 0 ⬝ᵥ n = b) (curvY : D 0 ⬝ᵥ n = c)
    (dA : HasDerivAt A U 0) (dB : HasDerivAt B V 0)
    (dC : HasDerivAt C P 0) (dD : HasDerivAt D Q 0) (dE : HasDerivAt E R 0) :
    HasDerivAt (fun s => meanJet (A s) (B s) (C s) (D s) (E s))
      (((P+R) ⬝ᵥ n + 2*(U ⬝ᵥ nx + V ⬝ᵥ ny))/(2*g)) 0 := by
  let K := fun s => A s ⨯₃ B s
  let T := fun s => meanCurvatureNumerator (A s) (B s) (C s) (D s) (E s)
  let delta := fun s => (A s ⬝ᵥ A s)*(B s ⬝ᵥ B s)-(A s ⬝ᵥ B s)^2
  let scale := fun s => 2*Real.sqrt (K s ⬝ᵥ K s)*delta s
  let J := (P+R) ⬝ᵥ n + 2*(U ⬝ᵥ nx + V ⬝ᵥ ny)
  have dk : DifferentiableAt ℝ K 0 :=
    (spatialCrossBilinear.hasFDerivAt_of_bilinear dA.hasFDerivAt dB.hasFDerivAt).differentiableAt
  have aa := real_vector_dot_hasDerivAt dA dA
  have ab := real_vector_dot_hasDerivAt dA dB
  have bb := real_vector_dot_hasDerivAt dB dB
  have diff := ((bb.mul (real_vector_dot_hasDerivAt dC dk.hasDerivAt)).sub
    ((ab.const_mul 2).mul (real_vector_dot_hasDerivAt dD dk.hasDerivAt))).add
    (aa.mul (real_vector_dot_hasDerivAt dE dk.hasDerivAt))
  have hx := congrArg (fun a => U ⬝ᵥ a) frame.scaled_normal_columns.1
  have hy := congrArg (fun a => V ⬝ᵥ a) frame.scaled_normal_columns.2
  simp only [dotProduct_smul,dotProduct_add,smul_eq_mul] at hx hy
  have dT : HasDerivAt T (g^2*J) 0 := by
    change HasDerivAt T _ 0 at diff
    apply diff.congr_deriv
    symm
    dsimp only [J,K]
    simp only [frame.aa,frame.bb,frame.ab,trace0,cross0,curvX,curvY,
      dotProduct_smul,smul_eq_mul,neg_dotProduct,add_dotProduct,
      dotProduct_comm (A 0) U,dotProduct_comm (B 0) V,dotProduct_comm (A 0) V]
    linear_combination 2*g*hx + 2*g*hy
  have zero : T 0 = 0 := by
    simp only [T,meanCurvatureNumerator,frame.aa,frame.bb,frame.ab,trace0,neg_dotProduct]
    ring
  have hkk : K 0 ⬝ᵥ K 0 = g^2 := by
    change (A 0 ⨯₃ B 0) ⬝ᵥ (A 0 ⨯₃ B 0)=_
    rw [cross0,smul_dotProduct,dotProduct_smul,smul_eq_mul,frame.nn]
    ring
  have sc : scale 0 = 2*g^3 := by
    simp only [scale,hkk,Real.sqrt_sq frame.metric_pos.le,delta,frame.aa,frame.bb,frame.ab]
    ring
  have nonsing : scale 0 ≠ 0 := by
    rw [sc]
    exact mul_ne_zero two_ne_zero (pow_ne_zero 3 frame.metric_pos.ne')
  have ds : DifferentiableAt ℝ scale 0 := by
    have kk := real_vector_dot_hasDerivAt dk.hasDerivAt dk.hasDerivAt
    have sqrt := kk.sqrt (by rw [hkk]; exact pow_ne_zero 2 frame.metric_pos.ne')
    exact ((sqrt.const_mul 2).mul ((aa.mul bb).sub (ab.pow 2))).differentiableAt
  have result := dT.div ds.hasDerivAt nonsing
  change HasDerivAt (T / scale) (J/(2*g)) 0
  apply result.congr_deriv
  rw [zero,sc]
  field_simp [frame.metric_pos.ne']
  ring

/-- A time-dependent two-jet whose first time derivative is the spatial
two-jet of W. In particular normal velocity satisfies the scalar Jacobi
equation if this family remains minimal to first order. -/
theorem derivative_mean_curvature_from_spatial_jets {F : ℝ → ℂ → Fin 3 → ℝ} {z : ℂ}
    (regular : ∀ᶠ w in 𝓝 z, (∀ j, HarmonicAt (fun p => F 0 p j) w) ∧
      ConformalCoordinateDerivatives (F 0) w ∧ Function.Injective (fderiv ℝ (F 0) w))
    {W : ℂ → Fin 3 → ℝ} (cw : ContDiffAt ℝ 2 W z)
    (first : ∀ v, HasDerivAt (fun s => fderiv ℝ (F s) z v) (fderiv ℝ W z v) 0)
    (second : ∀ v w, HasDerivAt (fun s => fderiv ℝ (fderiv ℝ (F s)) z v w)
      (fderiv ℝ (fderiv ℝ W) z v w) 0) :
    HasDerivAt (fun s => coordinateMeanCurvature (F s) z)
      (conformalSurfaceJacobi (F 0) (fun p => W p ⬝ᵥ harmonicChartNormal (F 0) p) z/2) 0 := by
  let X := F 0
  let N := harmonicChartNormal X
  let A := planePartial 1 X
  let B := planePartial I X
  let g := A z ⬝ᵥ A z
  let nx := planePartial 1 N z
  let ny := planePartial I N z
  let b := -(nx ⬝ᵥ A z)
  let c := -(nx ⬝ᵥ B z)
  have H : ConformalNormalFrame (A z) (B z) (N z) nx ny g b c := harmonic_chart_weingarten_frame regular
  have cx : AnalyticAt ℝ X z := analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (regular.self_of_nhds.1 j)
  have data := regular.mono fun w hw => harmonicChartNormal_data
    (analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (hw.1 j)) hw.2.1 hw.2.2
  have cn : DifferentiableAt ℝ N z := data.self_of_nhds.1.differentiableAt
  have hx := derivative_of_constant_pairing (X:=N) (Y:=A) cn (planePartial_analyticAt cx 1).differentiableAt
    (c:=0) (data.mono fun _ h => h.2.2.2.2.2.2.1) 1
  have hy := derivative_of_constant_pairing (X:=N) (Y:=B) cn (planePartial_analyticAt cx I).differentiableAt
    (c:=0) (data.mono fun _ h => h.2.2.2.2.2.2.2) 1
  let QX := fderiv ℝ (fderiv ℝ X) z
  let QW := fderiv ℝ (fderiv ℝ W) z
  have q (v w : ℂ) := c2_plane_second_column (show ContDiffAt ℝ 2 X z from cx.contDiffAt) v w
  have hcx : QX 1 1 ⬝ᵥ N z=b := by
    rw [dotProduct_comm (QX 1 1) (N z)]
    change N z ⬝ᵥ fderiv ℝ (fderiv ℝ X) z 1 1 = b
    rw [← q 1 1]
    exact eq_neg_of_add_eq_zero_left hx
  have hcy : QX 1 I ⬝ᵥ N z=c := by
    rw [dotProduct_comm (QX 1 I) (N z)]
    change N z ⬝ᵥ fderiv ℝ (fderiv ℝ X) z 1 I = c
    rw [← q 1 I]
    exact eq_neg_of_add_eq_zero_left hy
  have tr : QX I I = -QX 1 1 := by
    apply eq_neg_of_add_eq_zero_right
    have lap := harmonic_coordinate_laplacian_zero (X:=X) regular.self_of_nhds.1
    simpa only [laplacian_eq_iteratedFDeriv_complexPlane,iteratedFDeriv_two_apply,Matrix.cons_val_zero,
      Matrix.cons_val_one] using lap
  have cross : A z ⨯₃ B z = g • N z := by
    change _ = g • (g⁻¹ • (A z ⨯₃ B z))
    rw [smul_smul,mul_inv_cancel₀ H.metric_pos.ne',one_smul]
  have der := meanJet_derivative (A:=fun t => fderiv ℝ (F t) z 1)
    (B:=fun t => fderiv ℝ (F t) z I) (C:=fun t => fderiv ℝ (fderiv ℝ (F t)) z 1 1)
    (D:=fun t => fderiv ℝ (fderiv ℝ (F t)) z 1 I) (E:=fun t => fderiv ℝ (fderiv ℝ (F t)) z I I)
    H cross tr hcx hcy (first 1) (first I) (second 1 1) (second 1 I) (second I I)
  have J := jacobi_normal_velocity_identity regular cw
  change g*conformalSurfaceJacobi X (fun p => W p ⬝ᵥ N p) z =
    (Δ W) z ⬝ᵥ N z + 2*(planePartial 1 W z ⬝ᵥ nx + planePartial I W z ⬝ᵥ ny) at J
  have traceW : QW 1 1 + QW I I = (Δ W) z := by
    simp only [laplacian_eq_iteratedFDeriv_complexPlane,iteratedFDeriv_two_apply,Matrix.cons_val_zero,
      Matrix.cons_val_one,QW]
  have value : (((QW 1 1+QW I I) ⬝ᵥ N z+2*(planePartial 1 W z ⬝ᵥ nx +
      planePartial I W z ⬝ᵥ ny))/(2*g))=conformalSurfaceJacobi X (fun p => W p ⬝ᵥ N p) z/2 := by
    rw [traceW,← J]
    field_simp [H.metric_pos.ne']
  rw [← value]
  simpa only [coordinate_mean_eq_jet,QW,planePartial] using der

private theorem affine_direction_derivative (a v : V3) :
    HasDerivAt (fun t : ℝ => a+t • v) v 0 := by
  apply hasDerivAt_pi.mpr
  intro j
  change HasDerivAt (fun t : ℝ => a j+t*v j) (v j) 0
  simpa only [id_eq,one_mul] using ((hasDerivAt_id (0:ℝ)).mul_const (v j)).const_add (a j)

/-- The derivative of actual scalar mean curvature under the normal graph
X + t u N. Our H is the arithmetic mean of the two principal curvatures;
the linearization of 2H is the manuscript's Jacobi operator. -/
theorem actual_normal_graph_Jacobi_linearization {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (regular : ∀ᶠ w in 𝓝 z, (∀ j, HarmonicAt (fun p => X p j) w) ∧
      ConformalCoordinateDerivatives X w ∧ Function.Injective (fderiv ℝ X w))
    {u : ℂ → ℝ} (cu : ContDiffAt ℝ 2 u z) :
    HasDerivAt (fun t : ℝ => 2*coordinateMeanCurvature
      (fun p => X p+t • (u p • harmonicChartNormal X p)) z) (conformalSurfaceJacobi X u z) 0 := by
  let N := harmonicChartNormal X
  let W := fun p => u p • N p
  let F := fun (t : ℝ) (p : ℂ) => X p+t • W p
  have eq0 : F 0=X := by funext p; simp [F]
  have cx : ContDiffAt ℝ 2 X z := (analyticAt_pi_iff.mpr fun j =>
    _root_.HarmonicAt.analyticAt (regular.self_of_nhds.1 j)).contDiffAt
  have normal := regular.mono fun w hw => harmonicChartNormal_data
    (analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (hw.1 j)) hw.2.1 hw.2.2
  have cw : ContDiffAt ℝ 2 W z := cu.smul normal.self_of_nhds.1.contDiffAt
  have linear (t : ℝ) (p : ℂ) (x : DifferentiableAt ℝ X p) (w : DifferentiableAt ℝ W p) :
      fderiv ℝ (F t) p=fderiv ℝ X p+t • fderiv ℝ W p :=
    (x.hasFDerivAt.add (w.hasFDerivAt.const_smul t)).fderiv
  have linear2 (t : ℝ) : fderiv ℝ (fderiv ℝ (F t)) z =
      fderiv ℝ (fderiv ℝ X) z+t • fderiv ℝ (fderiv ℝ W) z := by
    have near : fderiv ℝ (F t) =ᶠ[𝓝 z] fun p => fderiv ℝ X p+t • fderiv ℝ W p := by
      filter_upwards [cx.eventually (by norm_num),cw.eventually (by norm_num)] with p x w
      exact linear t p (x.differentiableAt (by norm_num)) (w.differentiableAt (by norm_num))
    rw [near.fderiv_eq]
    have x := ((cx.fderiv_right (m:=1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
    have w := ((cw.fderiv_right (m:=1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
    exact (x.add (w.const_smul t)).fderiv
  have first (v : ℂ) : HasDerivAt (fun t => fderiv ℝ (F t) z v) (fderiv ℝ W z v) 0 := by
    apply (affine_direction_derivative (fderiv ℝ X z v) (fderiv ℝ W z v)).congr_of_eventuallyEq
    apply Filter.Eventually.of_forall
    intro t
    exact congrArg (fun D : ℂ →L[ℝ] V3 => D v)
      (linear t z (cx.differentiableAt (by norm_num)) (cw.differentiableAt (by norm_num)))
  have second (v w : ℂ) : HasDerivAt (fun t => fderiv ℝ (fderiv ℝ (F t)) z v w)
      (fderiv ℝ (fderiv ℝ W) z v w) 0 := by
    apply (affine_direction_derivative (fderiv ℝ (fderiv ℝ X) z v w)
      (fderiv ℝ (fderiv ℝ W) z v w)).congr_of_eventuallyEq
    apply Filter.Eventually.of_forall
    intro t
    exact congrArg (fun D : ℂ →L[ℝ] ℂ →L[ℝ] V3 => D v w) (linear2 t)
  have regF : ∀ᶠ w in 𝓝 z, (∀ j, HarmonicAt (fun p => F 0 p j) w) ∧
      ConformalCoordinateDerivatives (F 0) w ∧ Function.Injective (fderiv ℝ (F 0) w) := by
    rw [eq0]
    exact regular
  have h := derivative_mean_curvature_from_spatial_jets regF cw first second
  rw [eq0] at h
  have eq : (fun p => W p ⬝ᵥ N p) =ᶠ[𝓝 z] u := by
    filter_upwards [normal] with p hp
    change (u p • N p) ⬝ᵥ N p = u p
    rw [smul_dotProduct,smul_eq_mul,hp.2.2.2.2.2.1,mul_one]
  have field : conformalSurfaceJacobi X (fun p => W p ⬝ᵥ N p) z=conformalSurfaceJacobi X u z := by
    simp only [conformalSurfaceJacobi,(laplacian_congr_nhds eq).self_of_nhds,eq.self_of_nhds]
  change HasDerivAt (fun t => coordinateMeanCurvature (F t) z)
    (conformalSurfaceJacobi X (fun p => W p ⬝ᵥ N p) z/2) 0 at h
  rw [field] at h
  have dh := h.const_mul 2
  apply dh.congr_deriv
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.derivative_mean_curvature_from_spatial_jets
#print axioms TwoAxisHelicoid.actual_normal_graph_Jacobi_linearization
