import work_in_progress.OriginalProjectionNativeRowChecks
import work_in_progress.OriginalProjectionNativeGenerators
import work_in_progress.OriginalSparseNativeProgram

/-! Complete amplified output identity for the concrete 2,327-node sparse
native-symbol executor. Every one of the 2,048 original banks is retained.
The physical-symbol identification and the rational row checks are kernel
proofs. Connecting this sparse evaluator to the printed native RAM tape is
a separate compiler-composition statement.
-/
namespace FourierSchur.OriginalProjectionNativeOutputIdentity
open OAI.PowerSaving OAI.PowerSaving.Binary Matrix Finset
open OriginalNativeGeneratorSymbols OriginalSparseNativeRows
open OriginalProjectionNativeRowCertificate OriginalProjectionNativeRowChecks
open OriginalProjectionNativeGenerators
noncomputable section

theorem initial_certificate (i : ℕ) (hi : i<2048) :
    rowAt i=[⟨i,unitTag,1⟩] := initial_rows ⟨i,hi⟩

theorem causal_certificate (t : ℕ) (ht : t<3447) :
    ∀ p∈incomingAt t,p.1<2048+t := by
  have H := (node_checks ⟨t,ht⟩).2
  intro p hp
  exact of_decide_eq_true ((List.all_eq_true.mp H) p hp)

theorem rows_certificate (t : ℕ) (ht : t<3447) :
    nextRow directions (phaseAt t) rowAt (incomingAt t)=rowAt (2048+t) :=
  (node_checks ⟨t,ht⟩).1

theorem outputs_causal (i : Fin 2048) : ∀ p∈outputAt i.val,p.1<2048+3447 := by
  have H := (output_checks i).2
  intro p hp
  exact of_decide_eq_true ((List.all_eq_true.mp H) p hp)

/-- All original complex arrays, including every original auxiliary, have
the complete kernel as their output, for every tensor amplification. -/
theorem complete_output (f : ℕ) (x : ℕ → Sky (Fin 125) f → ℂ) (i : Fin 2048) :
    OriginalSparseNativeProgram.output 2048 3447 generators f x phaseAt incomingAt
      (outputAt i.val)=matAct f (kernel (Fin 125)) (x i.val) := by
  have H := OriginalSparseNativeProgram.output_rows 2048 3447 directions generators
    generators_square f x phaseAt incomingAt rowAt initial_certificate causal_certificate
    rows_certificate (outputAt i.val) (outputs_causal i) [⟨i.val,⟨1,0⟩,1⟩]
    (output_checks i).1
  rw [H]
  funext q
  simp [OriginalSparseNativeRows.act,mean,full_operator]

end
end FourierSchur.OriginalProjectionNativeOutputIdentity
