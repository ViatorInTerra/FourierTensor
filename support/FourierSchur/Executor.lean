import work_in_progress.OriginalCertifiedTensorBackend
import work_in_progress.OriginalGroupedCensusExecutor

/-!
# Public arbitrary-complex executor

This is the entry point for the strongest complete tensor program currently
proved in this project. It applies the profile-independent dense adapter to
the exact same-word census executor. The input consists of the order, the
fixed scalar I, and all independent coefficients. `Bill.OK` includes native
arithmetic, preparation, routing, validity, and the integer-register cap.

The density profile is a power saving, not polylogarithmic. The all-length
DFT endpoint remains `OriginalGroupedCensusExecutor.executeOne_census` with
its literal `fairwind` cost. Conditional improvement criteria are deliberately
kept in `FourierSchur.Research`.
-/

namespace FourierSchur.Executor

open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty OriginalSectorSubstitution
open OriginalCertifiedTensorBackend
noncomputable section

abbrev exponent : ℝ := OriginalGroupedCensusExecutor.exponent
abbrev density : Nat → Nat := OriginalGroupedCensusExecutor.profile

theorem exponent_eq : exponent = 1 - 1 / 100000000 := rfl

theorem exponent_pos_lt : 0 < exponent ∧ exponent < 1 :=
  ⟨OriginalGroupedCensusExecutor.exponent_pos,
    OriginalGroupedCensusExecutor.exponent_lt⟩

/-- The unchanged original dense tensor target. -/
abbrev transform (n : Nat) (input : Fin (2^n) → ℂ) : Fin (2^n) → ℂ :=
  tensorAction n fourierKernel input

/-- A certificate includes one fixed uniform native program and its bill. -/
abbrev Certificate (cl : Paint) (mode : Bool) := RawCertifiedFor density cl mode

theorem certificate_exists (cl : Paint) (mode : Bool) :
    Nonempty (Certificate cl mode) :=
  rawCertified_of_complete (OriginalGroupedCensusExecutor.complete_executor cl mode)

def backend (cl : Paint) (mode : Bool) : Certificate cl mode :=
  Classical.choice (certificate_exists cl mode)

/-- Every independent output is materialized in the ordinary dense layout. -/
theorem guarantee (cl : Paint) (mode : Bool) (n : Nat)
    (input : Fin (2^n) → ℂ) :
    (run (backend cl mode).program (rawInput cl n input)).OK
      (⟨2^n, transform n input⟩ : OAI.PowerSaving.Tape ℂ)
      ((backend cl mode).costConstant * (2^n * density n + 1))
      ((2^n + 2)^(backend cl mode).wordDegree) :=
  (backend cl mode).guarantee n input

theorem complete_executor (cl : Paint) (mode : Bool) :
    CompleteTensorExecutor cl mode density :=
  (backend cl mode).complete

end
end FourierSchur.Executor
