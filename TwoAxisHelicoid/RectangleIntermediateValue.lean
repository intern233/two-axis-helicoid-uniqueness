import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Order.IntermediateValue

namespace TwoAxisHelicoid
open Set Topology
open scoped unitInterval Topology

private theorem edge_stays_lt {T : Type*} [TopologicalSpace T] [PreconnectedSpace T] {u : T → ℝ}
    (cu : Continuous u) {k : ℝ} {a : T} (ha : u a<k) (no : ∀ p, u p ≠ k) (b : T) : u b<k := by
  by_contra! h
  obtain ⟨p,eq⟩ := intermediate_value_univ a b cu (show k ∈ Icc (u a) (u b) from ⟨ha.le,h⟩)
  exact no p eq

private theorem edge_stays_gt {T : Type*} [TopologicalSpace T] [PreconnectedSpace T] {u : T → ℝ}
    (cu : Continuous u) {k : ℝ} {a : T} (ha : k<u a) (no : ∀ p, u p ≠ k) (b : T) : k<u b := by
  by_contra! h
  obtain ⟨p,eq⟩ := intermediate_value_univ b a cu (show k ∈ Icc (u b) (u a) from ⟨h,ha.le⟩)
  exact no p eq

/-- A planar intermediate value principle on a rectangle. The first
coordinate has weak opposite signs on the vertical edges and the second
has strict opposite signs on the horizontal edges. A continuous
logarithm of a hypothetical nowhere-zero map is incompatible with
these four boundary inequalities. -/
theorem rectangle_intermediate_value_two_coordinates (F : unitInterval × unitInterval → ℂ)
    (cf : Continuous F) (left : ∀ y, (F (0,y)).re≤0) (right : ∀ y, 0≤(F (1,y)).re)
    (bottom : ∀ x, (F (x,0)).im<0) (top : ∀ x, 0<(F (x,1)).im) :
    ∃ q, F q=0 := by
  by_contra! no
  let : ContractibleSpace unitInterval := (convex_Icc (0:ℝ) 1).contractibleSpace ⟨0,left_mem_Icc.mpr zero_le_one⟩
  let : LocallyPathConnectedSpace unitInterval := (convex_Icc (0:ℝ) 1).locallyPathConnectedSpace
  let C : C(unitInterval × unitInterval,{v : ℂ // v ≠ 0}) := ⟨fun q => ⟨F q,no q⟩,cf.subtype_mk _⟩
  obtain ⟨G,⟨g₀,log⟩,_⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts C (0,0) (F (0,0)).log
    (Subtype.ext (Complex.exp_log (no _)))
  let θ := fun q => (G q).im
  have ct : Continuous θ := Complex.continuous_im.comp G.continuous
  have eq (q) : Complex.exp (G q)=F q := congrArg Subtype.val (congrFun log q)
  have cr (q) : (F q).re=Real.exp (G q).re * Real.cos (θ q) := (congrArg Complex.re (eq q)).symm.trans (Complex.exp_re _)
  have ci (q) : (F q).im=Real.exp (G q).re * Real.sin (θ q) := (congrArg Complex.im (eq q)).symm.trans (Complex.exp_im _)
  have sl (y) : Real.cos (θ (0,y))≤0 := nonpos_of_mul_nonpos_right (cr _ ▸ left y) (Real.exp_pos _)
  have sr (y) : 0≤Real.cos (θ (1,y)) := (mul_nonneg_iff_of_pos_left (Real.exp_pos _)).mp (cr _ ▸ right y)
  have sb (x) : Real.sin (θ (x,0))<0 := neg_of_mul_neg_right (ci _ ▸ bottom x) (Real.exp_pos _).le
  have st (x) : 0<Real.sin (θ (x,1)) := (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp (ci _ ▸ top x)
  have val : θ (0,0)=(F (0,0)).arg := by unfold θ; rw [g₀,Complex.log_im]
  have cb (y : unitInterval) : Continuous (fun x => θ (x,y)) := ct.comp (continuous_id.prodMk continuous_const)
  have cv (x : unitInterval) : Continuous (fun y => θ (x,y)) := ct.comp (continuous_const.prodMk continuous_id)
  have hl := edge_stays_gt (cb 0) (a := 0) (show -Real.pi<θ (0,0) by rw [val]; exact Complex.neg_pi_lt_arg _)
    (fun x he => by simpa [he] using sb x) 1
  have rightLo := edge_stays_gt (cv 1) (a := 0) hl
    (fun y he => by have h := sr y; rw [he] at h; norm_num at h) 1
  have topPos : 0<θ (1,1) := by
    by_contra! le
    exact (Real.sin_nonpos_of_nonpos_of_neg_pi_le le rightLo.le).not_gt (st 1)
  have originNeg : θ (0,1)<0 := edge_stays_lt (cv 0) (a := 0)
    (show θ (0,0)<0 by rw [val]; exact Complex.arg_neg_iff.mpr (bottom 0))
    (fun y he => by have h := sl y; rw [he] at h; norm_num at h) 1
  have originPos := edge_stays_gt (cb 1) (a := 1) topPos
    (fun x he => by simpa [he] using st x) 0
  exact originPos.not_ge originNeg.le

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rectangle_intermediate_value_two_coordinates
