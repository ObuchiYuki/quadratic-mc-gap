import SixVsSeven.Upper
import SixVsSeven.QLower
import SixVsSeven.MCLower

/-!
# Main theorem: `MC(Q) = 6 < 7 = qMC(Q)`
-/

namespace SixVsSeven

theorem six_vs_seven :
    (∃ C : Circuit (Fin 6) (Fin 5), C.size = 6 ∧ ComputesQ C) ∧
    (∀ C : Circuit (Fin 6) (Fin 5), ComputesQ C → 6 ≤ C.size) ∧
    (∃ C : Circuit (Fin 6) (Fin 5), C.IsQuadratic ∧ C.size = 7 ∧ ComputesQ C) ∧
    (∀ C : Circuit (Fin 6) (Fin 5), C.IsQuadratic → ComputesQ C → 7 ≤ C.size) :=
  ⟨mc_le_six, mc_ge_six, qmc_le_seven, qmc_ge_seven⟩

end SixVsSeven
