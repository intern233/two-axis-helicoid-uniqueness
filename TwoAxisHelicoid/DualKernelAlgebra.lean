import TwoAxisHelicoid.SigmaKernelAlgebra

namespace TwoAxisHelicoid
open Complex

theorem sigma_ratio_exponential_algebra (b w eta X d m s q : ℂ)
    (hd : d ≠ 0) (hs : s ≠ 0) (hq : q ≠ 0) :
    Complex.exp X*((Complex.exp (eta*(w-b)^2/2)*m/d)^2/
      ((Complex.exp (eta*w^2/2)*s/d)^2*(Complex.exp (eta*b^2/2)*q/d)^2)) =
      (d/q)^2*(m/s)^2*Complex.exp (X-2*eta*w*b) := by
  have he : Complex.exp X*Complex.exp (eta*(w-b)^2/2)^2 =
      Complex.exp (X-2*eta*w*b)*Complex.exp (eta*w^2/2)^2*Complex.exp (eta*b^2/2)^2 := by
    simp only [← Complex.exp_nat_mul,← Complex.exp_add]
    congr 1
    push_cast
    ring
  field_simp
  rw [show X-eta*w*b*2 = X-2*eta*w*b by ring]
  linear_combination m^2*he

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.sigma_ratio_exponential_algebra
