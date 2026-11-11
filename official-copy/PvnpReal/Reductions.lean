/-
  PvnpReal.Reductions — NP-hardness and basic facts about polynomial-time reductions.
-/
import PvnpReal.SatMachine

namespace PvnpReal

open Turing Computability

/-- NP-hardness: every NP language reduces to `L` in polynomial time. -/
def NPHard (L : Language) : Prop := ∀ L' : Language, InNP L' → PolyReduces L' L

theorem NPComplete_iff (L : Language) : NPComplete L ↔ InNP L ∧ NPHard L := Iff.rfl

/-- Since `SAT ∈ NP` is proved, Cook–Levin is now *exactly* the NP-hardness of SAT. -/
theorem cookLevin_iff_NPHard : CookLevinStatement ↔ NPHard SATLang :=
  ⟨fun h => h.2, fun h => ⟨SAT_in_NP, h⟩⟩

/-- Every language reduces to itself (Mathlib's identity machine, time `1`). -/
theorem PolyReduces.refl (L : Language) : PolyReduces L L :=
  ⟨id, ⟨idComputableInPolyTime strEnc⟩, fun _ => Iff.rfl⟩

end PvnpReal
