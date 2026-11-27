import TwoAxisHelicoid.RegularCutHalfPlaneCharts
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Compactness.Lindelof

namespace TwoAxisHelicoid
open Set Complex Filter Topology MeasureTheory
open scoped Topology ContDiff

/-- A regular zero of a C¹ scalar function has a neighborhood in which
its entire zero set has zero planar area. The inverse chart maps an
actual segment of the imaginary axis to the zero set. -/
theorem regular_scalar_zero_local_null {f : ℂ → ℝ} {x : ℂ} (sm : ContDiffAt ℝ 1 f x)
    (reg : ∃ w, fderiv ℝ f x w≠0) :
    ∃ U : Set ℂ, IsOpen U ∧ x∈U ∧ volume (U∩f ⁻¹' {0})=0 := by
  let A := fderiv ℝ f x
  let J : ℂ →L[ℝ] ℂ := I • (1 : ℂ →L[ℝ] ℂ)
  let B := A.comp J
  let Q := equivRealProdCLM.symm.toContinuousLinearMap
  let D := Q.comp (A.prod B)
  let g := fun z : ℂ => Q (f z,B z)
  obtain ⟨w,nw⟩ := reg
  have inj : Function.Injective D := by
    apply (injective_iff_map_eq_zero _).mpr
    intro v zero
    by_contra nv
    have a : A v=0 := congrArg Complex.re zero
    have b : A (I*v)=0 := congrArg Complex.im zero
    let c := w/v
    have eq : c.re • v+c.im • (I*v)=w := by
      rw [Complex.real_smul,Complex.real_smul,← mul_assoc,← add_mul,Complex.re_add_im]
      exact div_mul_cancel₀ _ nv
    apply nw
    change A w=0
    rw [← eq,map_add,map_smul,map_smul,a,b,smul_zero,smul_zero,zero_add]
  let E := (LinearEquiv.ofBijective D.toLinearMap
    ⟨inj,(LinearMap.injective_iff_surjective (f:=D.toLinearMap)).mp inj⟩).toContinuousLinearEquiv
  have df : HasFDerivAt g E.toContinuousLinearMap x :=
    Q.hasFDerivAt.comp x ((sm.differentiableAt one_ne_zero).hasFDerivAt.prodMk B.hasFDerivAt)
  have sg : ContDiffAt ℝ 1 g x := Q.contDiff.contDiffAt.comp x (sm.prodMk B.contDiff.contDiffAt)
  let e := sg.toOpenPartialHomeomorph g df one_ne_zero
  have ex : x∈e.source := sg.mem_toOpenPartialHomeomorph_source df one_ne_zero
  have back : ContDiffAt ℝ 1 e.symm (e x) := sg.to_localInverse df one_ne_zero
  obtain ⟨O,sub,op,marked⟩ := mem_nhds_iff.mp (back.eventually (by norm_num))
  let U := e.source∩e ⁻¹' O
  have ou : IsOpen U := e.isOpen_inter_preimage op
  let K := Complex.reCLM.ker
  have proper : K≠⊤ := by
    intro eq
    have mem : (1:ℂ)∈K := eq ▸ Submodule.mem_top
    exact one_ne_zero (show (1:ℝ)=0 from mem)
  have null : volume ((K:Set ℂ)∩O)=0 :=
    measure_mono_null inter_subset_left (Measure.addHaar_submodule volume K proper)
  refine ⟨U,ou,⟨ex,marked⟩,measure_mono_null ?_ (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    (f:=e.symm) (fun _ h => ((sub h.2).differentiableAt one_ne_zero).differentiableWithinAt) null)⟩
  rintro z ⟨⟨zs,zo⟩,zero⟩
  exact ⟨e z,⟨show f z=0 from zero,zo⟩,e.left_inv zs⟩

/-- The regular zeros of a scalar function on any subset of the
plane form a Lebesgue null set. No measurability of the subset is
required. -/
theorem regular_scalar_zero_set_null {S : Set ℂ} {f : ℂ → ℝ}
    (smooth : ∀ x∈S, ContDiffAt ℝ 1 f x)
    (zero : ∀ x∈S, f x=0) (reg : ∀ x∈S, ∃ w, fderiv ℝ f x w≠0) : volume S=0 := by
  classical
  choose U op inside null using fun x : S => regular_scalar_zero_local_null (smooth x.1 x.2) (reg x.1 x.2)
  obtain ⟨C,count,cover⟩ := TopologicalSpace.countable_cover_nhds (fun x : S =>
    ((op x).preimage continuous_subtype_val).mem_nhds (show x∈(Subtype.val : S → ℂ) ⁻¹' U x from inside x))
  let _ : Countable C := count.to_subtype
  refine measure_mono_null (t:=(⋃ i : C, U i.1∩f ⁻¹' {0})) ?_ (measure_iUnion_null fun i => null i.1)
  intro x hx
  obtain ⟨q,hq,hxq⟩ := mem_iUnion₂.mp
    (show (⟨x,hx⟩:S)∈⋃ q∈C, (Subtype.val : S → ℂ) ⁻¹' U q from cover.symm ▸ mem_univ _)
  exact mem_iUnion.mpr ⟨⟨q,hq⟩,hxq,zero x hx⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.regular_scalar_zero_set_null
