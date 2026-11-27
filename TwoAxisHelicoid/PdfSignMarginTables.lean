import TwoAxisHelicoid.CertificateData

namespace TwoAxisHelicoid.CertificateData

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Exact least reported lower bound and least negated upper bound in
the two sign tables printed in section 9.1. -/
theorem original_sign_table_exact_minima :
    (positiveData.map (fun r => r.hReal.lower)).min? =
      some (4048815533235523741519408834611/10384593717069655257060992658440192 : ℚ) ∧
    (negativeData.map (fun r => -r.hReal.upper)).min? =
      some (238070159187588210339310175778799/5192296858534827628530496329220096 : ℚ) := by
  constructor <;> decide +kernel

/-- In combination with the checked initial endpoint and adjacency,
the consecutive step sizes identify each row of the printed partition. -/
theorem original_sign_table_mesh :
    positiveData.map (fun r => r.t.upper-r.t.lower) =
      List.replicate 148 (1/6400) ++ List.replicate 126 (1/3200) ++ List.replicate 76 (1/1600) ++
      List.replicate 54 (1/800) ++ List.replicate 41 (1/400) ++ List.replicate 69 (1/200) ++
      List.replicate 6 (1/400) ++ List.replicate 4 (1/200) ++ List.replicate 18 (1/400) ++
      List.replicate 16 (1/800) ∧
    negativeData.map (fun r => r.t.upper-r.t.lower) =
      List.replicate 6 (1/400) ++ List.replicate 9 (1/200) ++ List.replicate 44 (1/100) := by
  constructor <;> decide +kernel

end TwoAxisHelicoid.CertificateData
#print axioms TwoAxisHelicoid.CertificateData.original_sign_table_exact_minima
#print axioms TwoAxisHelicoid.CertificateData.original_sign_table_mesh
