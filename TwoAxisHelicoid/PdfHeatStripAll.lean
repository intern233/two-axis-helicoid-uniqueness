import TwoAxisHelicoid.PdfHeatStripEdge00
import TwoAxisHelicoid.PdfHeatStripEdge01
import TwoAxisHelicoid.PdfHeatStripEdge02
import TwoAxisHelicoid.PdfHeatStripEdge03
import TwoAxisHelicoid.PdfHeatStripEdge04
import TwoAxisHelicoid.PdfHeatStripEdge05
import TwoAxisHelicoid.PdfHeatStripEdge06
import TwoAxisHelicoid.PdfHeatStripEdge07
import TwoAxisHelicoid.PdfHeatStripEdge08
import TwoAxisHelicoid.PdfHeatStripEdge09
import TwoAxisHelicoid.PdfHeatStripEdge10
import TwoAxisHelicoid.PdfHeatStripEdge11
import TwoAxisHelicoid.PdfHeatStripEdge12
import TwoAxisHelicoid.PdfHeatStripEdge13
import TwoAxisHelicoid.PdfHeatStripEdge14
import TwoAxisHelicoid.PdfHeatStripEdge15

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem original_heat_strip_edges {t a : ℝ} (tl : 17/20≤t) (tu : t≤9/10) (al : 147/250≤a) (au : a≤303/500) :
    ∀ z : ℂ, z.re∈Icc (-1:ℝ) 1 → |z.im|=3/16 →
      ‖pdfHeatKernel t a (-(thetaGt t a).re/(thetaGa t a).re) (z+Complex.I*((t/2:ℝ):ℂ))‖≤10^7 := by
  have ts : heatStripT.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have ps := heat_box_parameters_sound heatStripP_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) tl
  apply heat_grid_strip_bound ts ps tl
  intro k flag
  fin_cases k <;> cases flag
  · exact heatStripEdge00False
  · exact heatStripEdge00True
  · exact heatStripEdge01False
  · exact heatStripEdge01True
  · exact heatStripEdge02False
  · exact heatStripEdge02True
  · exact heatStripEdge03False
  · exact heatStripEdge03True
  · exact heatStripEdge04False
  · exact heatStripEdge04True
  · exact heatStripEdge05False
  · exact heatStripEdge05True
  · exact heatStripEdge06False
  · exact heatStripEdge06True
  · exact heatStripEdge07False
  · exact heatStripEdge07True
  · exact heatStripEdge08False
  · exact heatStripEdge08True
  · exact heatStripEdge09False
  · exact heatStripEdge09True
  · exact heatStripEdge10False
  · exact heatStripEdge10True
  · exact heatStripEdge11False
  · exact heatStripEdge11True
  · exact heatStripEdge12False
  · exact heatStripEdge12True
  · exact heatStripEdge13False
  · exact heatStripEdge13True
  · exact heatStripEdge14False
  · exact heatStripEdge14True
  · exact heatStripEdge15False
  · exact heatStripEdge15True
  · exact heatStripEdge16False
  · exact heatStripEdge16True
  · exact heatStripEdge17False
  · exact heatStripEdge17True
  · exact heatStripEdge18False
  · exact heatStripEdge18True
  · exact heatStripEdge19False
  · exact heatStripEdge19True
  · exact heatStripEdge20False
  · exact heatStripEdge20True
  · exact heatStripEdge21False
  · exact heatStripEdge21True
  · exact heatStripEdge22False
  · exact heatStripEdge22True
  · exact heatStripEdge23False
  · exact heatStripEdge23True
  · exact heatStripEdge24False
  · exact heatStripEdge24True
  · exact heatStripEdge25False
  · exact heatStripEdge25True
  · exact heatStripEdge26False
  · exact heatStripEdge26True
  · exact heatStripEdge27False
  · exact heatStripEdge27True
  · exact heatStripEdge28False
  · exact heatStripEdge28True
  · exact heatStripEdge29False
  · exact heatStripEdge29True
  · exact heatStripEdge30False
  · exact heatStripEdge30True
  · exact heatStripEdge31False
  · exact heatStripEdge31True
  · exact heatStripEdge32False
  · exact heatStripEdge32True
  · exact heatStripEdge33False
  · exact heatStripEdge33True
  · exact heatStripEdge34False
  · exact heatStripEdge34True
  · exact heatStripEdge35False
  · exact heatStripEdge35True
  · exact heatStripEdge36False
  · exact heatStripEdge36True
  · exact heatStripEdge37False
  · exact heatStripEdge37True
  · exact heatStripEdge38False
  · exact heatStripEdge38True
  · exact heatStripEdge39False
  · exact heatStripEdge39True
  · exact heatStripEdge40False
  · exact heatStripEdge40True
  · exact heatStripEdge41False
  · exact heatStripEdge41True
  · exact heatStripEdge42False
  · exact heatStripEdge42True
  · exact heatStripEdge43False
  · exact heatStripEdge43True
  · exact heatStripEdge44False
  · exact heatStripEdge44True
  · exact heatStripEdge45False
  · exact heatStripEdge45True
  · exact heatStripEdge46False
  · exact heatStripEdge46True
  · exact heatStripEdge47False
  · exact heatStripEdge47True
  · exact heatStripEdge48False
  · exact heatStripEdge48True
  · exact heatStripEdge49False
  · exact heatStripEdge49True
  · exact heatStripEdge50False
  · exact heatStripEdge50True
  · exact heatStripEdge51False
  · exact heatStripEdge51True
  · exact heatStripEdge52False
  · exact heatStripEdge52True
  · exact heatStripEdge53False
  · exact heatStripEdge53True
  · exact heatStripEdge54False
  · exact heatStripEdge54True
  · exact heatStripEdge55False
  · exact heatStripEdge55True
  · exact heatStripEdge56False
  · exact heatStripEdge56True
  · exact heatStripEdge57False
  · exact heatStripEdge57True
  · exact heatStripEdge58False
  · exact heatStripEdge58True
  · exact heatStripEdge59False
  · exact heatStripEdge59True
  · exact heatStripEdge60False
  · exact heatStripEdge60True
  · exact heatStripEdge61False
  · exact heatStripEdge61True
  · exact heatStripEdge62False
  · exact heatStripEdge62True
  · exact heatStripEdge63False
  · exact heatStripEdge63True

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.original_heat_strip_edges
