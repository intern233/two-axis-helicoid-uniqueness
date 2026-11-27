import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace TwoAxisHelicoid
open Function Metric Set Topology Filter
open scoped Topology ContDiff

/-- At a simple zero in the second coordinate, the whole zero locus is a
single graph over the first coordinate and inherits the smoothness of
the defining function. -/
theorem regular_plane_zero_graph {n : ℕ∞ω} (hn : n≠0) {F : ℝ×ℝ → ℝ} {p : ℝ×ℝ}
    (smooth : ContDiffAt ℝ n F p) (zero : F p=0) (nz : fderiv ℝ F p (0,1)≠0) :
    ∃ φ : ℝ → ℝ, ContDiffAt ℝ n φ p.1 ∧ φ p.1=p.2 ∧ (∀ᶠ r in 𝓝 p.1, F (r,φ r)=0) ∧
      ∀ᶠ q in 𝓝 p, F q=0 ↔ q.2=φ q.1 := by
  let A := fderiv ℝ F p
  let L := (ContinuousLinearMap.fst ℝ ℝ ℝ).prod A
  let T := fun q : ℝ×ℝ => (q.1,F q)
  have ds := (smooth.differentiableAt hn).hasFDerivAt
  have inj : Injective L := by
    apply (injective_iff_map_eq_zero _).mpr
    intro w eq
    have x : w.1=0 := congrArg Prod.fst eq
    have y : A w=0 := congrArg Prod.snd eq
    have repr : w=w.2 • ((0,1):ℝ×ℝ) := by apply Prod.ext <;> simp [x]
    have val := congrArg A repr
    rw [y,map_smul,smul_eq_mul] at val
    exact Prod.ext x ((mul_eq_zero.mp val.symm).resolve_right nz)
  let D := (LinearEquiv.ofBijective L.toLinearMap
    ⟨inj,(LinearMap.injective_iff_surjective (f:=L.toLinearMap)).mp inj⟩).toContinuousLinearEquiv
  have dT : HasFDerivAt T D.toContinuousLinearMap p := hasFDerivAt_fst.prodMk ds
  have sT : ContDiffAt ℝ n T p := contDiffAt_fst.prodMk smooth
  let e := sT.toOpenPartialHomeomorph T dT hn
  have src : p∈e.source := sT.mem_toOpenPartialHomeomorph_source dT hn
  have ec : e p=(p.1,0) := Prod.ext rfl zero
  have back : ContDiffAt ℝ n e.symm (p.1,0) := by
    rw [← ec]
    exact sT.to_localInverse dT hn
  let φ := fun x : ℝ => (e.symm (x,0)).2
  have sp : ContDiffAt ℝ n φ p.1 := (back.comp p.1 (contDiffAt_id.prodMk contDiffAt_const)).snd
  have atp : φ p.1=p.2 := congrArg Prod.snd (show e.symm (p.1,0)=p by rw [← ec,e.left_inv src])
  have zf : ∀ᶠ x in 𝓝 p.1, F (x,φ x)=0 := by
    have m : (p.1,(0:ℝ))∈e.target := by rw [← ec]; exact e.map_source src
    have c : Continuous (fun x : ℝ => (x,(0:ℝ))) := continuous_id.prodMk continuous_const
    filter_upwards [c.continuousAt.eventually (e.open_target.mem_nhds m)] with x hx
    have fixed := e.right_inv hx
    have fst : (e.symm (x,0)).1=x := congrArg Prod.fst fixed
    change F (x,(e.symm (x,0)).2)=0
    nth_rw 1 [← fst]
    exact congrArg Prod.snd fixed
  refine ⟨φ,sp,atp,zf,?_⟩
  filter_upwards [e.open_source.mem_nhds src,continuous_fst.continuousAt.eventually zf] with q inside vanishes
  constructor
  · intro h
    have eq : e q=(q.1,0) := Prod.ext rfl h
    exact congrArg Prod.snd ((e.left_inv inside).symm.trans (congrArg e.symm eq))
  · intro h
    have pair : q=(q.1,φ q.1) := Prod.ext rfl h
    exact (congrArg F pair).trans vanishes

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.regular_plane_zero_graph
