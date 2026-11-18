import work_in_progress.OriginalProjectionNativeTapeMetadata
namespace FourierSchur.OriginalProjectionNativeTapeImplementation
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty Matrix Finset
open OriginalNativeBankDAG OriginalProjectionFrameAlphabet OriginalProjectionNativeTapeMetadata
noncomputable section
abbrev Role := Fin 2048⊕Fin 3447
def bases : Role→OBase (Fin 125)
  | .inl _ => OBase.canonical (Fin 125)
  | .inr i => modeBase (modeAt i.val)
def nodes : List (Node (Fin 125) (Fin 2048) (Fin 3447)) := List.ofFn nativeNode
def outputs : Matrix (Fin 2048) Role ℚ := outputCoeff
def program := programWord nodes outputs
theorem program_semantics (f : ℕ) (x : Data (Fin 125) Role f) :
    OriginalGroupedFrameWords.walk bases f program x=evaluate bases f nodes outputs x :=
  programWord_correct bases f nodes outputs x
theorem scratch_cleared (f : ℕ) (x : Data (Fin 125) Role f) (i : Fin 3447) :
    evaluate bases f nodes outputs x (.inr i)=0 := evaluate_scratch bases f nodes outputs x i
section Native
universe U
variable {ι : Type U} {m : Bool} {cl : Paint} {f : ι→ℕ}
  {s : Ty} {x : ι→T s} {r : ℕ}
  {v : ∀ i,Grain (Fin 125) (Fin 2048) r (f i)}
theorem program_native (b : Bank (hatch cl) ι)
    (h : Rig m b.B f s x cl (Layout.std 125) (Layout.std 2048) r v)
    (R : Layout Role) (tau : ι→ℕ→ℕ)
    (HC : ∀ k : ℕ,0<k → k≤125 → GroupedResidual.Rig.RawContract cl b
      (fun i => k*f i) (fun i => tau i (k*f i))) :
    Able m b s (bundle cl) x
      (fun i => (fleet (Layout.std 125) R r (f i)).tape
        (OriginalGroupedWordRAM.coastline bases r (f i) program
          (OriginalLocalizedBankWorkspaceRAM.padded (κ:=Fin 3447) (v i))))
      (fun i => (fleet (Layout.std 125) (Layout.std 2048) r (f i)).n)
      (fun i => (nodes.map (nodeCharge (Layout.std 125) r (f i) (tau i))).sum) :=
  fresh_native b h R (0 : Fin 2048) (by decide) bases tau HC nodes outputs
end Native
end
end FourierSchur.OriginalProjectionNativeTapeImplementation
