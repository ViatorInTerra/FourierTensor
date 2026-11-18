import work_in_progress.OriginalScratchGroupedInstantiationRAM
import work_in_progress.OriginalStrictSquareRootMargin
import work_in_progress.OriginalPolylogExecutor

/-!
End-to-end reduction to one finite, physical shared-block certificate.

The hypotheses are the actual original-output semantics of a native bank
DAG and a strict moment of that same DAG's complete callback inventory.
There is no supplied fast executor, recursive correctness oracle, separate
profile bound, or uncharged scratch-width denominator.  The present best
projection DAG does NOT satisfy the strict-moment hypothesis.
-/
namespace FourierSchur.OriginalSharedBlockCompletion
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty
open OAI.PowerSaving.Selection OAI.PowerSaving.Skies OAI.PowerSaving.Slant
open OriginalNativeBankDAG OriginalScratchGroupedBodyRAM
open OriginalSectorSubstitution OriginalCompilerRootBridge
open OriginalStrictSquareRootMargin
open Filter Asymptotics
noncomputable section
set_option maxHeartbeats 1000000

variable {α : Type*} {η κ : Type} [Fintype α] [DecidableEq α]
  [Fintype η] [DecidableEq η] [Fintype κ] [DecidableEq κ]

/-- Supplied preparation registers can be ignored by a closed executor;
the projection and its routing are actual constant-work RAM code. -/
theorem supplied_of_complete {cl : Paint} {m : Bool} {profile : ℕ→ℕ}
    (h : CompleteTensorExecutor cl m profile) (s : Ty) (table : ℕ→T s) :
    SuppliedTensorExecutor s table cl m profile := by
  have hp : Can m (fun i : TensorInput => 2^i.1)
      (suppliedIn s cl) (simIn cl)
      (fun i => suppliedBits s cl table i.1 i.2)
      (fun i => givenBits cl i.1 i.2)
      (fun i => 2^i.1*profile i.1) :=
    Can.pair Can.first (Can.pair Can.second.fst Can.second.snd.snd)
  exact Can.then_do hp h

/-- Every local native fee, spectator copy, scratch initialization and
cleanup, remnant and original-role conversion is paid by `grouped_program`.
The strict moment supplies the entire subsequent asymptotic argument. -/
theorem closed_executors_of_strict_sqrt
    (X : Layout α) (R0 : Layout η) (R : Layout (η⊕κ)) (j : η)
    (a : ℕ) (ha : 0<a) (hR : R0.n=2^a) (hu : 3≤X.n)
    (A : (η⊕κ)→OBase α) (nodes : List (Node α η κ))
    (D : Matrix η (η⊕κ) ℚ) (Hsem : KernelDAG A nodes D)
    (hM : OriginalGroupedWordProfile.moment (programWord nodes D) X.n a (1/2)<1) :
    ∃ (z C : ℝ), 0<z ∧ z<1/2 ∧ Monotone (powerProfile z) ∧
      OriginalSchurDensitySufficiency.SqrtLogProfile (powerProfile z) C ∧
      ∀ (cl : Paint) (m : Bool), CompleteTensorExecutor cl m (powerProfile z) := by
  let P := programWord nodes D
  have hcard : Fintype.card α=X.n := X.card
  have hpos : 0<Fintype.card α := by omega
  have hm : finiteMoment (Fintype.card α) a
      (OriginalGroupedWordProfile.rank P) (OriginalGroupedWordProfile.weight P) (1/2)<1 := by
    simpa only [finiteMoment,OriginalGroupedWordProfile.moment,hcard,P] using hM
  obtain ⟨z,c,C,hz,hhalf,hmono,hprofile,hbound⟩ :=
    allowance_profile_of_strict_sqrt (Fintype.card α) a (a+Fintype.card α)
      (OriginalGroupedWordProfile.rank P) (OriginalGroupedWordProfile.weight P)
      hpos ha (Nat.le_add_right _ _) le_rfl (OriginalGroupedWordProfile.rank_le P)
      (fun q hq => by simp [OriginalGroupedWordProfile.weight,hq]) hm
  refine ⟨z,C,hz,hhalf,hmono,hprofile,fun cl m => ?_⟩
  have H := OriginalScratchGroupedInstantiationRAM.grouped_program
    cl m X R0 R j a ha hR hu A nodes D Hsem
    (fun i : TensorInput => i.1) (fun i => i.2)
  exact H.weaken ⟨c,fun i => hbound i.1⟩

/-- A strict complete finite inventory gives one uniformly charged program
for every positive DFT length and arbitrary independent complex input.
The integer-register cap remains polynomial in the input width. -/
theorem executeOne_of_strict_shared_block
    (X : Layout α) (R0 : Layout η) (R : Layout (η⊕κ)) (j : η)
    (a : ℕ) (ha : 0<a) (hR : R0.n=2^a) (hu : 3≤X.n)
    (A : (η⊕κ)→OBase α) (nodes : List (Node α η κ))
    (D : Matrix η (η⊕κ) ℚ) (Hsem : KernelDAG A nodes D)
    (hM : OriginalGroupedWordProfile.moment (programWord nodes D) X.n a (1/2)<1) :
    ∃ (z : ℝ) (program : Prog false dftInKind dftOutKind) (d C p : ℕ),
      0<z ∧ z<1/2 ∧
      (∀ (n : ℕ), 0<n → ∀ x : Vec n,
        (run program (n,root (receipt n),(⟨n,x⟩ : Tape ℂ))).OK
          (⟨n,dft n x⟩ : Tape ℂ)
          (C*(OriginalAllLengthSubstitution.fairwind (powerProfile z) d n+1)) ((n+2)^p)) ∧
      (fun n : ℕ =>
        ((C*(OriginalAllLengthSubstitution.fairwind (powerProfile z) d n+1) : ℕ) : ℝ))
        =O[atTop] (fun n : ℕ => (n:ℝ)*Real.sqrt (Real.log ((n:ℝ)+2))) := by
  obtain ⟨z,B,hz,hhalf,hmono,hprofile,hExec⟩ :=
    closed_executors_of_strict_sqrt X R0 R j a ha hR hu A nodes D Hsem hM
  obtain ⟨program,d,C,p,hprogram,hcost⟩ :=
    OriginalSchurDensitySufficiency.executeOne_sqrtLog
      (supplied_of_complete (hExec .left false) sc parentRoot)
      (supplied_of_complete (hExec .scalar false) sc parentRoot) hmono hprofile
  exact ⟨z,program,d,C,p,hz,hhalf,hprogram,
    hcost.trans OriginalPolylogExecutor.flight_bigO_shifted⟩

end
end FourierSchur.OriginalSharedBlockCompletion
