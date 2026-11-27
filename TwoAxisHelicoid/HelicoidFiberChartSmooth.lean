import TwoAxisHelicoid.HelicoidFiberChart

namespace TwoAxisHelicoid
open Set
open scoped Topology ContDiff

theorem helicoidFiberChart_contDiff : ContDiff ℝ (∞ : WithTop ℕ∞) helicoidFiberChart :=
  helicoidTubeMap_contDiff.comp (show ContDiff ℝ (∞ : WithTop ℕ∞)
    (fun x : ℝ × (ℝ × ℝ) => ((x.1,x.2.1),x.2.2)) by fun_prop)

theorem helicoidFiberChart_symm_contDiffAt {y : HelicoidTubeCoordinates}
    (hy : y ∈ helicoidFiberChart.target) :
    ContDiffAt ℝ (∞ : WithTop ℕ∞) helicoidFiberChart.symm y :=
  (helicoidTubeEquiv_inverse_contDiffAt hy).fst.fst.prodMk
    ((helicoidTubeEquiv_inverse_contDiffAt hy).fst.snd.prodMk
      (helicoidTubeEquiv_inverse_contDiffAt hy).snd)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoidFiberChart_symm_contDiffAt
