import work_in_progress.OriginalProjectionNativeTapeAllNodes
import work_in_progress.OriginalProjectionNativeTapeImplementation
import work_in_progress.OriginalProjectionNativeOutputIdentity
import work_in_progress.OriginalNativeSparseExecutionBridge

/-! Composition of the concrete printed native RAM tape with its complete
amplified output certificate. Every original role is preserved, and all
fresh scratch roles are cleared by the final native point pass.
-/
namespace FourierSchur.OriginalProjectionNativeTapeCorrectness
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty Matrix Finset
open OriginalNativeBankDAG OriginalSparsePointGather OriginalNativeGeneratorSymbols
open OriginalProjectionFrameAlphabet OriginalNativeSparseExecutionBridge
open OriginalProjectionNativeRowCertificate OriginalProjectionNativeGenerators
open OriginalProjectionNativeTapeMetadata OriginalProjectionNativeTapeAllNodes
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 30000

def payload (t : ℕ) : Node (Fin 125) (Fin 2048) (Fin 3447) :=
  nativeNode ⟨t%3447,Nat.mod_lt _ (by decide)⟩

theorem payload_lt (t : ℕ) (ht : t<3447) : payload t=nativeNode ⟨t,ht⟩ := by
  simp [payload,Nat.mod_eq_of_lt ht]

theorem payload_slot (t : ℕ) (ht : t<3447) :
    encodeRole (Q:=2048) (Sum.inr (payload t).slot)=2048+t := by
  rw [payload_lt t ht]
  rfl

theorem payload_coeff (t : ℕ) (ht : t<3447) :
    (payload t).coeff=lookupCoeff (decodeInputs 2048 3447 (incomingAt t)) := by
  rw [payload_lt t ht]
  rfl

theorem payload_nodup (t : ℕ) (ht : t<3447) :
    ((decodeInputs 2048 3447 (incomingAt t)).map Prod.fst).Nodup :=
  (data_checks ⟨t,ht⟩).2.2

theorem payload_bounds (t : ℕ) (ht : t<3447) : ∀ p∈incomingAt t,p.1<2048+3447 := by
  intro p hp
  have H := OriginalProjectionNativeOutputIdentity.causal_certificate t ht p hp
  omega

theorem payload_operator (t : ℕ) (ht : t<3447) :
    shift (payload t).offset*(frame (OriginalProjectionNativeTapeImplementation.bases (.inr (payload t).slot))
      (payload t).targetMask*unframe (OriginalProjectionNativeTapeImplementation.bases (.inr (payload t).slot))
        (payload t).sourceMask)=operator generators (phaseAt t) := by
  rw [payload_lt t ht]
  change shift (OriginalBinaryMatrixCertificates.wordVector 125 (offsetAt t))*
    (frame (OriginalProjectionNativeTapeImplementation.bases (.inr ⟨t,ht⟩)) (modeMask (modeAt t))*
      unframe (OriginalProjectionNativeTapeImplementation.bases (.inr ⟨t,ht⟩)) ∅)=_
  have hu (A : OBase (Fin 125)) : unframe A ∅=1 := by
    simp [unframe,OBase.proj,wrap_one]
  rw [hu,mul_one]
  change shift (OriginalBinaryMatrixCertificates.wordVector 125 (offsetAt t))*
    frame (modeBase (modeAt t)) (modeMask (modeAt t))=_
  rw [← native_operator (modeAt t) (data_checks ⟨t,ht⟩).2.1 (offsetAt t),
    ← (data_checks ⟨t,ht⟩).1]

theorem nodes_eq : OriginalProjectionNativeTapeImplementation.nodes=
    List.ofFn (fun i : Fin 3447 => payload i.val) := by
  unfold OriginalProjectionNativeTapeImplementation.nodes
  apply congrArg List.ofFn
  funext i
  exact (payload_lt i.val i.isLt).symm

theorem folded_state (f : ℕ) (x : Data (Fin 125) Role f) :
    OriginalProjectionNativeTapeImplementation.nodes.foldl
      (fun y g => nodeValue OriginalProjectionNativeTapeImplementation.bases f g y) x=
      nativeState OriginalProjectionNativeTapeImplementation.bases f payload x 3447 := by
  rw [nodes_eq]
  exact fold_nativeState OriginalProjectionNativeTapeImplementation.bases f payload x 3447

theorem native_state (f : ℕ) (x : Data (Fin 125) Role f) :
    ∀ j,nativeState OriginalProjectionNativeTapeImplementation.bases f payload x 3447 j=
      OriginalSparseNativeProgram.execute 2048 generators f (extendData x) phaseAt incomingAt
        3447 (encodeRole j) :=
  state_correspondence OriginalProjectionNativeTapeImplementation.bases generators f payload phaseAt incomingAt
    payload_slot payload_coeff payload_nodup payload_bounds payload_operator x 3447 (by omega)

theorem evaluate_original_kernel (f : ℕ) (x : Data (Fin 125) Role f) (i : Fin 2048) :
    evaluate OriginalProjectionNativeTapeImplementation.bases f OriginalProjectionNativeTapeImplementation.nodes
      OriginalProjectionNativeTapeImplementation.outputs x (.inl i)=matAct f (kernel (Fin 125)) (x (.inl i)) := by
  funext q
  rw [evaluate_original,folded_state]
  change (∑ j,(lookupCoeff (decodeInputs 2048 3447 (outputAt i.val)) j:ℂ)*
    nativeState OriginalProjectionNativeTapeImplementation.bases f payload x 3447 j q)=_
  rw [output_correspondence OriginalProjectionNativeTapeImplementation.bases generators f payload phaseAt incomingAt
    x (native_state f x) (outputAt i.val) (output_nodup i)
    (OriginalProjectionNativeOutputIdentity.outputs_causal i) q,
    OriginalProjectionNativeOutputIdentity.complete_output]
  simp [extendData,decodeRole,i.isLt]

theorem word_original_kernel (f : ℕ) (x : Data (Fin 125) Role f) (i : Fin 2048) :
    OriginalGroupedFrameWords.walk OriginalProjectionNativeTapeImplementation.bases f OriginalProjectionNativeTapeImplementation.program x
      (.inl i)=matAct f (kernel (Fin 125)) (x (.inl i)) := by
  rw [OriginalProjectionNativeTapeImplementation.program_semantics]
  exact evaluate_original_kernel f x i

theorem word_scratch_zero (f : ℕ) (x : Data (Fin 125) Role f) (i : Fin 3447) :
    OriginalGroupedFrameWords.walk OriginalProjectionNativeTapeImplementation.bases f OriginalProjectionNativeTapeImplementation.program x
      (.inr i)=0 := by
  rw [OriginalProjectionNativeTapeImplementation.program_semantics]
  exact OriginalProjectionNativeTapeImplementation.scratch_cleared f x i

def kernelGrain {r f : ℕ} (v : Grain (Fin 125) (Fin 2048) r f) :
    Grain (Fin 125) (Fin 2048) r f := fun q =>
  matAct f (kernel (Fin 125)) (fun z => v (q.1,q.2.1,z)) q.2.2

theorem coastline_kernel {r f : ℕ} (v : Grain (Fin 125) (Fin 2048) r f) :
    OriginalGroupedWordRAM.coastline OriginalProjectionNativeTapeImplementation.bases r f OriginalProjectionNativeTapeImplementation.program
      (OriginalLocalizedBankWorkspaceRAM.padded (κ:=Fin 3447) v)=
        OriginalLocalizedBankWorkspaceRAM.padded (κ:=Fin 3447) (kernelGrain v) := by
  funext q
  rcases q with ⟨role,s,z⟩
  cases role with
  | inl i =>
    change OriginalGroupedFrameWords.walk OriginalProjectionNativeTapeImplementation.bases f OriginalProjectionNativeTapeImplementation.program
      (fun l j => OriginalLocalizedBankWorkspaceRAM.padded v (l,s,j)) (.inl i) z=_
    rw [word_original_kernel]
    rfl
  | inr i =>
    change OriginalGroupedFrameWords.walk OriginalProjectionNativeTapeImplementation.bases f OriginalProjectionNativeTapeImplementation.program
      (fun l j => OriginalLocalizedBankWorkspaceRAM.padded v (l,s,j)) (.inr i) z=_
    rw [word_scratch_zero]
    rfl

section Native
universe U
variable {ι : Type U} {m : Bool} {cl : Paint} {f : ι→ℕ}
  {s : Ty} {x : ι→T s} {r : ℕ}
  {v : ∀ i,Grain (Fin 125) (Fin 2048) r (f i)}

/-- Fully charged native execution with the actual complete-kernel output,
including every original auxiliary and cleared fresh scratch. Recursive
child contracts remain explicit and their spectator prices are unchanged. -/
theorem native_kernel (b : Bank (hatch cl) ι)
    (h : Rig m b.B f s x cl (Layout.std 125) (Layout.std 2048) r v)
    (R : Layout Role) (tau : ι→ℕ→ℕ)
    (HC : ∀ k : ℕ,0<k → k≤125 → GroupedResidual.Rig.RawContract cl b
      (fun i => k*f i) (fun i => tau i (k*f i))) :
    Able m b s (bundle cl) x
      (fun i => (fleet (Layout.std 125) R r (f i)).tape
        (OriginalLocalizedBankWorkspaceRAM.padded (κ:=Fin 3447) (kernelGrain (v i))))
      (fun i => (fleet (Layout.std 125) (Layout.std 2048) r (f i)).n)
      (fun i => (OriginalProjectionNativeTapeImplementation.nodes.map
        (nodeCharge (Layout.std 125) r (f i) (tau i))).sum) := by
  simpa only [coastline_kernel] using OriginalProjectionNativeTapeImplementation.program_native b h R tau HC

end Native
end
end FourierSchur.OriginalProjectionNativeTapeCorrectness
