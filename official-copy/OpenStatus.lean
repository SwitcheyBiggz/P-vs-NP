/-
  Restates the open P versus NP proposition already in `PvnpReal`.
  Neither direction is proved here.
-/
import PvnpReal

namespace PvnpReal

theorem P_eq_NP_stated : P_eq_NP = (∀ L : Language, InP L ↔ InNP L) := rfl

theorem P_eq_NP_still_sat : P_eq_NP ↔ InP SATLang := P_eq_NP_iff_SAT_in_P

end PvnpReal
