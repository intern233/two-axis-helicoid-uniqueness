import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Complex

theorem sigma_kernel_algebra (a z eta r d m s b : ℂ)
    (hd : d ≠ 0) (hs : s ≠ 0) (hb : b ≠ 0) :
    Complex.exp (2*(a-1)*(r+eta*z)+2*eta*z)*
      ((Complex.exp (eta*(z-a)^2/2)*m/d)^2/
        ((Complex.exp (eta*z^2/2)*s/d)^2*(Complex.exp (eta*a^2/2)*b/d)^2)) =
      (d/b)^2*(m/s)^2*Complex.exp (2*(a-1)*r) := by
  have he : Complex.exp (2*((a-1)*(r+eta*z)+eta*z))*
      Complex.exp (eta*(z-a)^2/2)^2 =
      Complex.exp (2*(a-1)*r)*Complex.exp (eta*z^2/2)^2*Complex.exp (a^2*eta/2)^2 := by
    simp only [← Complex.exp_nat_mul,← Complex.exp_add]
    congr 1
    push_cast
    ring
  field_simp
  linear_combination m^2*he

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.sigma_kernel_algebra
