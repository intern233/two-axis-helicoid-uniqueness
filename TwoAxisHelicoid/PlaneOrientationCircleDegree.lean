import Mathlib.Topology.Covering.FundamentalGroupCircle
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Algebra.Module.LocallyConvex

namespace TwoAxisHelicoid
open Set Function Filter Topology
open scoped Topology

abbrev OrientationCircle := AddCircle (1:ℝ)

theorem orientationCircle_int_zero (n : ℤ) : ((n:ℝ) : OrientationCircle) = 0 :=
  (AddCircle.coe_eq_zero_iff (1:ℝ)).mpr ⟨n,by simp⟩

/-- Two real lifts of the same circle map on a connected space differ by
a single integer constant. -/
theorem orientationCircle_lifts_difference {E : Type*} [TopologicalSpace E] [PreconnectedSpace E]
    {F G : E → ℝ} (hF : Continuous F) (hG : Continuous G)
    (h : ∀ x, (F x : OrientationCircle) = (G x : OrientationCircle)) (a : E) :
    ∃ n : ℤ, ∀ x, F x = G x + n := by
  have h0 : ((F a-G a:ℝ) : OrientationCircle) = 0 := by rw [AddCircle.coe_sub,h a,sub_self]
  obtain ⟨n,hn⟩ := (AddCircle.coe_eq_zero_iff (1:ℝ)).mp h0
  have hn' : (n:ℝ) = F a-G a := by simpa using hn
  refine ⟨n,?_⟩
  have hcomp : ((↑) : ℝ → OrientationCircle) ∘ F = ((↑) : ℝ → OrientationCircle) ∘ (fun x => G x+n) := by
    funext x
    change (F x:OrientationCircle) = ((G x+n:ℝ):OrientationCircle)
    rw [AddCircle.coe_add,orientationCircle_int_zero,add_zero,h x]
  have he : F = fun x => G x+n := (AddCircle.isCoveringMap_coe (1:ℝ)).eq_of_comp_eq hF
    (hG.add continuous_const) hcomp a (by linarith)
  exact congrFun he

/-- Translation of a real lift upon increasing the argument by one
defines the integer degree, independently of basepoints. -/
def HasOrientationCircleDegree (f : OrientationCircle → OrientationCircle) (n : ℤ) : Prop :=
  ∃ F : ℝ → ℝ, Continuous F ∧ (∀ x : ℝ, (F x : OrientationCircle) = f (x:OrientationCircle)) ∧
    ∀ x : ℝ, F (x+1) = F x+n

theorem orientationCircle_degree_exists {f : OrientationCircle → OrientationCircle} (hf : Continuous f) :
    ∃ n : ℤ, HasOrientationCircleDegree f n := by
  let π : ℝ → OrientationCircle := (↑)
  let h : C(ℝ,OrientationCircle) := ⟨f ∘ π,hf.comp QuotientAddGroup.continuous_mk⟩
  obtain ⟨b,hb⟩ := (Quotient.mk_surjective : Surjective π) (h 0)
  obtain ⟨F,⟨_,hF⟩,_⟩ := (AddCircle.isCoveringMap_coe (1:ℝ)).existsUnique_continuousMap_lifts h 0 b hb
  have hl (x : ℝ) : (F x : OrientationCircle) = f (x:OrientationCircle) := congrFun hF x
  obtain ⟨n,hn⟩ := orientationCircle_lifts_difference
    (F.continuous.comp (continuous_id.add continuous_const)) F.continuous
    (fun x => by change (F (x+1):OrientationCircle) = (F x:OrientationCircle); rw [hl,hl,AddCircle.coe_add_period]) 0
  exact ⟨n,F,F.continuous,hl,hn⟩

theorem HasOrientationCircleDegree.unique {f : OrientationCircle → OrientationCircle} {n m : ℤ}
    (hn : HasOrientationCircleDegree f n) (hm : HasOrientationCircleDegree f m) : n = m := by
  obtain ⟨F,hF,hπF,hFn⟩ := hn
  obtain ⟨G,hG,hπG,hGm⟩ := hm
  obtain ⟨k,hk⟩ := orientationCircle_lifts_difference hF hG (fun x => (hπF x).trans (hπG x).symm) 0
  have hzero := hk 0
  have hone := hk (0+1)
  rw [hFn,hGm] at hone
  exact_mod_cast (by linarith : (n:ℝ) = (m:ℝ))

theorem orientationCircle_lift_integer_shift {F : ℝ → ℝ} {d : ℤ}
    (h : ∀ x : ℝ, F (x+1) = F x+d) (k : ℤ) (x : ℝ) : F (x+k) = F x+k*d := by
  have hper : Function.Periodic (fun y : ℝ => F y-d*y) 1 := by
    intro y
    change F (y+1)-d*(y+1) = F y-d*y
    rw [h]
    ring
  have hs := hper.int_mul k x
  change F (x+k*1)-d*(x+k*1) = F x-d*x at hs
  rw [mul_one] at hs
  linear_combination hs

theorem HasOrientationCircleDegree.comp {f g : OrientationCircle → OrientationCircle} {n m : ℤ}
    (hf : HasOrientationCircleDegree f n) (hg : HasOrientationCircleDegree g m) :
    HasOrientationCircleDegree (f ∘ g) (n*m) := by
  obtain ⟨F,hF,hπF,hFn⟩ := hf
  obtain ⟨G,hG,hπG,hGm⟩ := hg
  refine ⟨F ∘ G,hF.comp hG,fun x => (hπF (G x)).trans (congrArg f (hπG x)),?_⟩
  intro x
  change F (G (x+1)) = F (G x)+((n*m:ℤ):ℝ)
  rw [hGm,orientationCircle_lift_integer_shift hFn]
  push_cast
  ring

theorem orientationCircle_degree_id : HasOrientationCircleDegree id 1 :=
  ⟨id,continuous_id,fun _ => rfl,fun _ => by simp⟩

theorem orientationCircle_degree_neg : HasOrientationCircleDegree (fun x => -x) (-1) :=
  ⟨fun x => -x,continuous_neg,fun x => AddCircle.coe_neg _,fun x => by push_cast; ring⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.orientationCircle_degree_exists
#print axioms TwoAxisHelicoid.HasOrientationCircleDegree.comp
