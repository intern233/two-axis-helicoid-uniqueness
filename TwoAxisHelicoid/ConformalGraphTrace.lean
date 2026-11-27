import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace TwoAxisHelicoid

/-- For a conformal tangent frame, the trace of a graph Hessian splits
into its minimal-graph operator and a combination of the two first
derivatives of the height difference. The identity is polynomial and
allows vertical tangent planes. -/
theorem conformal_graph_hessian_trace (a b c d u v p q xx xy yy : ℝ)
    (equal : a^2+c^2+u^2=b^2+d^2+v^2) (orth : a*b+c*d+u*v=0) :
    let metricFactor := a^2+c^2+u^2
    let j := a*d-b*c
    let s := c*v-d*u
    let t := u*b-a*v
    let e := u-p*a-q*c
    let h := v-p*b-q*d
    let A := yy*(s-p*j)-2*xy*t
    let B := xx*(t-q*j)+2*xy*p*j
    metricFactor*(xx*(a^2+b^2)+2*xy*(a*c+b*d)+yy*(c^2+d^2)) =
      j^2*((1+q^2)*xx-2*p*q*xy+(1+p^2)*yy) +
      (-d*A+b*B)*e+(c*A-a*B)*h := by
  dsimp only
  linear_combination (xx*a^2+2*xy*a*c+yy*c^2)*equal +
    (2*xx*a*b+2*xy*(a*d+b*c)+2*yy*c*d)*orth

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.conformal_graph_hessian_trace
