import TwoAxisHelicoid.PdfPrimalGridSampling
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.CertificateSemantics

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalStripT := Grid.ofRats (7/5) (141/100)
def rightPrimalStripP : PrimalThetaParameters := ⟨⟨⟨14408839182133102165303,14868691741796214871495,true⟩,⟨0,0,true⟩⟩, ⟨⟨1709078613136318001614789,1898976236818203650136812,true⟩,⟨0,0,true⟩⟩, ⟨(-379795247363668217818059),34359738368,true⟩, ⟨2810056053083694696853357,3932380344222399331080289,true⟩⟩
theorem rightPrimalStripP_ok : rightPrimalStripP.encloses (primalThetaParameters rightPrimalStripT (Grid.ofRats (9/10) 1)) := by decide +kernel

theorem rightPrimalStripEdge0False : let out := primalStripOutput rightPrimalStripT rightPrimalStripP (-1+(0:ℚ)/8) (-1+((0:ℚ)+1)/8) (-3/8) (-3/8)
  out.ok=true ∧ out.mag≤4096*Grid.denom := by decide +kernel
theorem rightPrimalStripEdge0True : let out := primalStripOutput rightPrimalStripT rightPrimalStripP (-1+(0:ℚ)/8) (-1+((0:ℚ)+1)/8) (3/8) (3/8)
  out.ok=true ∧ out.mag≤4096*Grid.denom := by decide +kernel
theorem rightPrimalStripEdge1False : let out := primalStripOutput rightPrimalStripT rightPrimalStripP (-1+(1:ℚ)/8) (-1+((1:ℚ)+1)/8) (-3/8) (-3/8)
  out.ok=true ∧ out.mag≤4096*Grid.denom := by decide +kernel
theorem rightPrimalStripEdge1True : let out := primalStripOutput rightPrimalStripT rightPrimalStripP (-1+(1:ℚ)/8) (-1+((1:ℚ)+1)/8) (3/8) (3/8)
  out.ok=true ∧ out.mag≤4096*Grid.denom := by decide +kernel
theorem rightPrimalStripEdge2False : let out := primalStripOutput rightPrimalStripT rightPrimalStripP (-1+(2:ℚ)/8) (-1+((2:ℚ)+1)/8) (-3/8) (-3/8)
  out.ok=true ∧ out.mag≤4096*Grid.denom := by decide +kernel
theorem rightPrimalStripEdge2True : let out := primalStripOutput rightPrimalStripT rightPrimalStripP (-1+(2:ℚ)/8) (-1+((2:ℚ)+1)/8) (3/8) (3/8)
  out.ok=true ∧ out.mag≤4096*Grid.denom := by decide +kernel
theorem rightPrimalStripEdge3False : let out := primalStripOutput rightPrimalStripT rightPrimalStripP (-1+(3:ℚ)/8) (-1+((3:ℚ)+1)/8) (-3/8) (-3/8)
  out.ok=true ∧ out.mag≤4096*Grid.denom := by decide +kernel
theorem rightPrimalStripEdge3True : let out := primalStripOutput rightPrimalStripT rightPrimalStripP (-1+(3:ℚ)/8) (-1+((3:ℚ)+1)/8) (3/8) (3/8)
  out.ok=true ∧ out.mag≤4096*Grid.denom := by decide +kernel
theorem rightPrimalStripEdge4False : let out := primalStripOutput rightPrimalStripT rightPrimalStripP (-1+(4:ℚ)/8) (-1+((4:ℚ)+1)/8) (-3/8) (-3/8)
  out.ok=true ∧ out.mag≤4096*Grid.denom := by decide +kernel
theorem rightPrimalStripEdge4True : let out := primalStripOutput rightPrimalStripT rightPrimalStripP (-1+(4:ℚ)/8) (-1+((4:ℚ)+1)/8) (3/8) (3/8)
  out.ok=true ∧ out.mag≤4096*Grid.denom := by decide +kernel
theorem rightPrimalStripEdge5False : let out := primalStripOutput rightPrimalStripT rightPrimalStripP (-1+(5:ℚ)/8) (-1+((5:ℚ)+1)/8) (-3/8) (-3/8)
  out.ok=true ∧ out.mag≤4096*Grid.denom := by decide +kernel
theorem rightPrimalStripEdge5True : let out := primalStripOutput rightPrimalStripT rightPrimalStripP (-1+(5:ℚ)/8) (-1+((5:ℚ)+1)/8) (3/8) (3/8)
  out.ok=true ∧ out.mag≤4096*Grid.denom := by decide +kernel
theorem rightPrimalStripEdge6False : let out := primalStripOutput rightPrimalStripT rightPrimalStripP (-1+(6:ℚ)/8) (-1+((6:ℚ)+1)/8) (-3/8) (-3/8)
  out.ok=true ∧ out.mag≤4096*Grid.denom := by decide +kernel
theorem rightPrimalStripEdge6True : let out := primalStripOutput rightPrimalStripT rightPrimalStripP (-1+(6:ℚ)/8) (-1+((6:ℚ)+1)/8) (3/8) (3/8)
  out.ok=true ∧ out.mag≤4096*Grid.denom := by decide +kernel
theorem rightPrimalStripEdge7False : let out := primalStripOutput rightPrimalStripT rightPrimalStripP (-1+(7:ℚ)/8) (-1+((7:ℚ)+1)/8) (-3/8) (-3/8)
  out.ok=true ∧ out.mag≤4096*Grid.denom := by decide +kernel
theorem rightPrimalStripEdge7True : let out := primalStripOutput rightPrimalStripT rightPrimalStripP (-1+(7:ℚ)/8) (-1+((7:ℚ)+1)/8) (3/8) (3/8)
  out.ok=true ∧ out.mag≤4096*Grid.denom := by decide +kernel

theorem right_original_full_strip_edges {t a : ℝ} (tL : (7/5:ℝ)≤t) (tU : t≤141/100) (aL : (9/10:ℝ)≤a) (aU : a≤1) :
  ∀ z : ℂ, z.re∈Icc (-1:ℝ) 0 → |z.im|=3/8 → ‖thetaA t a (z+Complex.I*((t/2:ℝ):ℂ))‖≤4096 := by
  have hT : rightPrimalStripT.Contains t := Grid.contains_rats (by push_cast; exact tL) (by push_cast; exact tU)
  have hP := primal_box_parameters_sound rightPrimalStripP_ok (t:=t) (a:=a) (by push_cast; exact tL) (by push_cast; exact tU) (by push_cast; exact aL) (by push_cast; exact aU) (by linarith)
  apply right_strip_bound_of_eight hT hP (by linarith)
  intro i flag
  fin_cases i <;> cases flag
  · exact rightPrimalStripEdge0False
  · exact rightPrimalStripEdge0True
  · exact rightPrimalStripEdge1False
  · exact rightPrimalStripEdge1True
  · exact rightPrimalStripEdge2False
  · exact rightPrimalStripEdge2True
  · exact rightPrimalStripEdge3False
  · exact rightPrimalStripEdge3True
  · exact rightPrimalStripEdge4False
  · exact rightPrimalStripEdge4True
  · exact rightPrimalStripEdge5False
  · exact rightPrimalStripEdge5True
  · exact rightPrimalStripEdge6False
  · exact rightPrimalStripEdge6True
  · exact rightPrimalStripEdge7False
  · exact rightPrimalStripEdge7True

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.right_original_full_strip_edges
