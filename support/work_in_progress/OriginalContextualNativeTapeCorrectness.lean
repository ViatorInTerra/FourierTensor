import work_in_progress.OriginalContextualNativeTapeAllNodes
import work_in_progress.OriginalContextualNativeTapeImplementation
import work_in_progress.OriginalContextualNativeOutputIdentity
import work_in_progress.OriginalNativeSparseExecutionBridge

/-! Composition of the concrete printed native RAM tape with its complete
amplified output certificate. Every original role is preserved, and all
fresh scratch roles are cleared by the final native point pass.
-/
namespace FourierSchur.OriginalContextualNativeTapeCorrectness
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty Matrix Finset
open OriginalNativeBankDAG OriginalSparsePointGather OriginalNativeGeneratorSymbols
open OriginalNativeFrameAlphabet OriginalNativeSparseExecutionBridge
open OriginalContextualNativeRowCertificate OriginalJointNativeGenerators
open OriginalContextualNativeTapeMetadata OriginalContextualNativeTapeAllNodes
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 30000

def payload (t : ℕ) : Node (Fin 216) (Fin 2048) (Fin 2327) :=
  nativeNode ⟨t%2327,Nat.mod_lt _ (by decide)⟩

theorem payload_lt (t : ℕ) (ht : t<2327) : payload t=nativeNode ⟨t,ht⟩ := by
  simp [payload,Nat.mod_eq_of_lt ht]

theorem payload_slot (t : ℕ) (ht : t<2327) :
    encodeRole (Q:=2048) (Sum.inr (payload t).slot)=2048+t := by
  rw [payload_lt t ht]
  rfl

theorem payload_coeff (t : ℕ) (ht : t<2327) :
    (payload t).coeff=lookupCoeff (decodeInputs 2048 2327 (incomingAt t)) := by
  rw [payload_lt t ht]
  rfl

theorem payload_nodup (t : ℕ) (ht : t<2327) :
    ((decodeInputs 2048 2327 (incomingAt t)).map Prod.fst).Nodup :=
  (data_checks ⟨t,ht⟩).2.2

theorem payload_bounds (t : ℕ) (ht : t<2327) : ∀ p∈incomingAt t,p.1<2048+2327 := by
  intro p hp
  have H := OriginalContextualNativeOutputIdentity.causal_certificate t ht p hp
  omega

theorem payload_operator (t : ℕ) (ht : t<2327) :
    shift (payload t).offset*(frame (OriginalContextualNativeTapeImplementation.bases (.inr (payload t).slot))
      (payload t).targetMask*unframe (OriginalContextualNativeTapeImplementation.bases (.inr (payload t).slot))
        (payload t).sourceMask)=operator generators (phaseAt t) := by
  rw [payload_lt t ht]
  change shift (OriginalBinaryMatrixCertificates.wordVector 216 (offsetAt t))*
    (frame (OriginalContextualNativeTapeImplementation.bases (.inr ⟨t,ht⟩)) (modeMask (modeAt t))*
      unframe (OriginalContextualNativeTapeImplementation.bases (.inr ⟨t,ht⟩)) ∅)=_
  have hu (A : OBase (Fin 216)) : unframe A ∅=1 := by
    simp [unframe,OBase.proj,wrap_one]
  rw [hu,mul_one]
  change shift (OriginalBinaryMatrixCertificates.wordVector 216 (offsetAt t))*
    frame (modeBase (modeAt t)) (modeMask (modeAt t))=_
  rw [← native_operator (modeAt t) (data_checks ⟨t,ht⟩).2.1 (offsetAt t),
    ← (data_checks ⟨t,ht⟩).1]

theorem nodes_eq : OriginalContextualNativeTapeImplementation.nodes=
    List.ofFn (fun i : Fin 2327 => payload i.val) := by
  unfold OriginalContextualNativeTapeImplementation.nodes
  apply congrArg List.ofFn
  funext i
  exact (payload_lt i.val i.isLt).symm

theorem folded_state (f : ℕ) (x : Data (Fin 216) Role f) :
    OriginalContextualNativeTapeImplementation.nodes.foldl
      (fun y g => nodeValue OriginalContextualNativeTapeImplementation.bases f g y) x=
      nativeState OriginalContextualNativeTapeImplementation.bases f payload x 2327 := by
  rw [nodes_eq]
  exact fold_nativeState OriginalContextualNativeTapeImplementation.bases f payload x 2327

theorem native_state (f : ℕ) (x : Data (Fin 216) Role f) :
    ∀ j,nativeState OriginalContextualNativeTapeImplementation.bases f payload x 2327 j=
      OriginalSparseNativeProgram.execute 2048 generators f (extendData x) phaseAt incomingAt
        2327 (encodeRole j) :=
  state_correspondence OriginalContextualNativeTapeImplementation.bases generators f payload phaseAt incomingAt
    payload_slot payload_coeff payload_nodup payload_bounds payload_operator x 2327 (by omega)

theorem evaluate_original_kernel (f : ℕ) (x : Data (Fin 216) Role f) (i : Fin 2048) :
    evaluate OriginalContextualNativeTapeImplementation.bases f OriginalContextualNativeTapeImplementation.nodes
      OriginalContextualNativeTapeImplementation.outputs x (.inl i)=matAct f (kernel (Fin 216)) (x (.inl i)) := by
  funext q
  rw [evaluate_original,folded_state]
  change (∑ j,(lookupCoeff (decodeInputs 2048 2327 (outputAt i.val)) j:ℂ)*
    nativeState OriginalContextualNativeTapeImplementation.bases f payload x 2327 j q)=_
  rw [output_correspondence OriginalContextualNativeTapeImplementation.bases generators f payload phaseAt incomingAt
    x (native_state f x) (outputAt i.val) (output_nodup i)
    (OriginalContextualNativeOutputIdentity.outputs_causal i) q,
    OriginalContextualNativeOutputIdentity.complete_output]
  simp [extendData,decodeRole,i.isLt]

theorem word_original_kernel (f : ℕ) (x : Data (Fin 216) Role f) (i : Fin 2048) :
    OriginalGroupedFrameWords.walk OriginalContextualNativeTapeImplementation.bases f OriginalContextualNativeTapeImplementation.program x
      (.inl i)=matAct f (kernel (Fin 216)) (x (.inl i)) := by
  rw [OriginalContextualNativeTapeImplementation.program_semantics]
  exact evaluate_original_kernel f x i

theorem word_scratch_zero (f : ℕ) (x : Data (Fin 216) Role f) (i : Fin 2327) :
    OriginalGroupedFrameWords.walk OriginalContextualNativeTapeImplementation.bases f OriginalContextualNativeTapeImplementation.program x
      (.inr i)=0 := by
  rw [OriginalContextualNativeTapeImplementation.program_semantics]
  exact OriginalContextualNativeTapeImplementation.scratch_cleared f x i

def kernelGrain {r f : ℕ} (v : Grain (Fin 216) (Fin 2048) r f) :
    Grain (Fin 216) (Fin 2048) r f := fun q =>
  matAct f (kernel (Fin 216)) (fun z => v (q.1,q.2.1,z)) q.2.2

theorem coastline_kernel {r f : ℕ} (v : Grain (Fin 216) (Fin 2048) r f) :
    OriginalGroupedWordRAM.coastline OriginalContextualNativeTapeImplementation.bases r f OriginalContextualNativeTapeImplementation.program
      (OriginalLocalizedBankWorkspaceRAM.padded (κ:=Fin 2327) v)=
        OriginalLocalizedBankWorkspaceRAM.padded (κ:=Fin 2327) (kernelGrain v) := by
  funext q
  rcases q with ⟨role,s,z⟩
  cases role with
  | inl i =>
    change OriginalGroupedFrameWords.walk OriginalContextualNativeTapeImplementation.bases f OriginalContextualNativeTapeImplementation.program
      (fun l j => OriginalLocalizedBankWorkspaceRAM.padded v (l,s,j)) (.inl i) z=_
    rw [word_original_kernel]
    rfl
  | inr i =>
    change OriginalGroupedFrameWords.walk OriginalContextualNativeTapeImplementation.bases f OriginalContextualNativeTapeImplementation.program
      (fun l j => OriginalLocalizedBankWorkspaceRAM.padded v (l,s,j)) (.inr i) z=_
    rw [word_scratch_zero]
    rfl

section Native
universe U
variable {ι : Type U} {m : Bool} {cl : Paint} {f : ι→ℕ}
  {s : Ty} {x : ι→T s} {r : ℕ}
  {v : ∀ i,Grain (Fin 216) (Fin 2048) r (f i)}

/-- Fully charged native execution with the actual complete-kernel output,
including every original auxiliary and cleared fresh scratch. Recursive
child contracts remain explicit and their spectator prices are unchanged. -/
theorem native_kernel (b : Bank (hatch cl) ι)
    (h : Rig m b.B f s x cl (Layout.std 216) (Layout.std 2048) r v)
    (R : Layout Role) (tau : ι→ℕ→ℕ)
    (HC : ∀ k : ℕ,0<k → k≤216 → GroupedResidual.Rig.RawContract cl b
      (fun i => k*f i) (fun i => tau i (k*f i))) :
    Able m b s (bundle cl) x
      (fun i => (fleet (Layout.std 216) R r (f i)).tape
        (OriginalLocalizedBankWorkspaceRAM.padded (κ:=Fin 2327) (kernelGrain (v i))))
      (fun i => (fleet (Layout.std 216) (Layout.std 2048) r (f i)).n)
      (fun i => (OriginalContextualNativeTapeImplementation.nodes.map
        (nodeCharge (Layout.std 216) r (f i) (tau i))).sum) := by
  simpa only [coastline_kernel] using OriginalContextualNativeTapeImplementation.program_native b h R tau HC

end Native
end
end FourierSchur.OriginalContextualNativeTapeCorrectness
