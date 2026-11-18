import work_in_progress.OriginalCompilerRootBridge
import work_in_progress.OriginalSectorSubstitution

/-! The actual upstream tensor algorithm inhabits the replacement interface.
Its closed RAM program projects (k,I,parentRoot,input) to (k,I,input) and
runs the checked hills_program.  This retains its executed-work and integer
bound; the hills profile does not supply the desired faster Schur density. -/
namespace FourierSchur.OriginalStandardTensorExecutor
open OriginalCompilerRootBridge OriginalSectorSubstitution
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open OAI.PowerSaving.Binary
noncomputable section
universe U

theorem standard_complete (cl : Paint) (m : Bool) :
    CompleteTensorExecutor cl m hills :=
  hills_program cl m (fun i : TensorInput => i.1) (fun i => i.2)

/-- The extra supplied root is an available register, and the ordinary
upstream algorithm simply leaves it unused.  No scalar table is smuggled
into an I-only executor certificate. -/
theorem standard_supplied (cl : Paint) (m : Bool) :
    SuppliedTensorExecutor sc parentRoot cl m hills := by
  have hp : Can m (fun i : TensorInput => 2^i.1)
      (suppliedIn sc cl) (simIn cl)
      (fun i => suppliedBits sc cl parentRoot i.1 i.2)
      (fun i => givenBits cl i.1 i.2)
      (fun i => 2^i.1*hills i.1) :=
    Can.pair Can.first (Can.pair Can.second.fst Can.second.snd.snd)
  exact Can.then_do hp (standard_complete cl m)

theorem standard_run (cl : Paint) (m : Bool) {ι : Type U}
    (k : ι→Nat) (v : ∀ i,Bits (k i)→ℂ) :
    Can m (fun i => 2^k i) (suppliedIn sc cl) (bundle cl)
      (fun i => suppliedBits sc cl parentRoot (k i) (v i))
      (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*hills (k i)) :=
  SuppliedTensorExecutor.run (standard_supplied cl m) k v

end
end FourierSchur.OriginalStandardTensorExecutor
