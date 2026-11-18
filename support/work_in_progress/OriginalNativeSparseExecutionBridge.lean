import work_in_progress.OriginalSparsePointGather
import work_in_progress.OriginalSparseNativeProgram

/-! Exact native-register/sparse-evaluator correspondence. The hypotheses
are local payload equalities and reference bounds checked for the printed
program, not assumptions about the data or a fast execution oracle.
-/
namespace FourierSchur.OriginalNativeSparseExecutionBridge
open OAI.PowerSaving OAI.PowerSaving.Binary Matrix Finset
open OriginalNativeBankDAG OriginalSparsePointGather OriginalNativeGeneratorSymbols
noncomputable section

variable {n Q K k : ℕ} [NeZero K]

def extendData (x : Data (Fin n) (Fin Q⊕Fin K) f) : ℕ → Sky (Fin n) f → ℂ :=
  fun j => x (decodeRole Q K j)

def nativeState (A : (Fin Q⊕Fin K) → OBase (Fin n)) (f : ℕ)
    (payload : ℕ → Node (Fin n) (Fin Q) (Fin K))
    (x : Data (Fin n) (Fin Q⊕Fin K) f) : ℕ → Data (Fin n) (Fin Q⊕Fin K) f
  | 0 => x
  | t+1 => nodeValue A f (payload t) (nativeState A f payload x t)

theorem fold_nativeState (A : (Fin Q⊕Fin K) → OBase (Fin n)) (f : ℕ)
    (payload : ℕ → Node (Fin n) (Fin Q) (Fin K))
    (x : Data (Fin n) (Fin Q⊕Fin K) f) (t : ℕ) :
    (List.ofFn (fun i : Fin t => payload i.val)).foldl (fun y g => nodeValue A f g y) x=
      nativeState A f payload x t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [List.ofFn_succ_last,List.foldl_append]
    simpa only [Fin.val_castSucc,Fin.val_last,List.foldl_cons,List.foldl_nil,nativeState] using
      congrArg (nodeValue A f (payload t)) ih

theorem state_correspondence (A : (Fin Q⊕Fin K) → OBase (Fin n))
    (generators : Fin k → Space (Fin n) → ℂ) (f : ℕ)
    (payload : ℕ → Node (Fin n) (Fin Q) (Fin K))
    (phaseAt : ℕ → Tag) (incomingAt : ℕ → List (ℕ×ℚ))
    (hslot : ∀ t,t<K → encodeRole (Q:=Q) (Sum.inr (payload t).slot)=Q+t)
    (hcoeff : ∀ t,t<K → (payload t).coeff=lookupCoeff (decodeInputs Q K (incomingAt t)))
    (hnodup : ∀ t,t<K → ((decodeInputs Q K (incomingAt t)).map Prod.fst).Nodup)
    (hbound : ∀ t,t<K → ∀ p∈incomingAt t,p.1<Q+K)
    (hoperator : ∀ t,t<K →
      shift (payload t).offset*(frame (A (.inr (payload t).slot)) (payload t).targetMask*
        unframe (A (.inr (payload t).slot)) (payload t).sourceMask)=operator generators (phaseAt t))
    (x : Data (Fin n) (Fin Q⊕Fin K) f) :
    ∀ t,t≤K → ∀ j,
      nativeState A f payload x t j=
        OriginalSparseNativeProgram.execute Q generators f (extendData x) phaseAt incomingAt t (encodeRole j) := by
  intro t
  induction t with
  | zero => intro _ j; simp [nativeState,OriginalSparseNativeProgram.execute,extendData,decode_encode]
  | succ t ih =>
    intro ht j
    have htk : t<K := by omega
    by_cases hj : j=Sum.inr (payload t).slot
    · subst j
      rw [nativeState,nodeValue,if_pos rfl,OriginalSparseNativeProgram.execute,hslot t htk,
        Function.update_self,hoperator t htk]
      congr 1
      funext q
      rw [hcoeff t htk,decoded_gather Q K _ (hnodup t htk)]
      apply congrArg List.sum
      apply List.map_congr_left
      intro p hp
      rw [congr_fun (ih (by omega) (decodeRole Q K p.1)) q,
        encode_decode Q K p.1 (hbound t htk p hp)]
    · have hne : encodeRole j≠Q+t := by
        intro he
        have hz : encodeRole j=encodeRole (Q:=Q) (Sum.inr (payload t).slot) := by
          rw [hslot t htk,he]
        exact hj (encode_injective Q K hz)
      rw [nativeState,nodeValue,if_neg hj,OriginalSparseNativeProgram.execute,Function.update_of_ne hne]
      exact ih (by omega) j

theorem output_correspondence (A : (Fin Q⊕Fin K) → OBase (Fin n))
    (generators : Fin k → Space (Fin n) → ℂ) (f : ℕ)
    (payload : ℕ → Node (Fin n) (Fin Q) (Fin K))
    (phaseAt : ℕ → Tag) (incomingAt : ℕ → List (ℕ×ℚ))
    (x : Data (Fin n) (Fin Q⊕Fin K) f)
    (hstate : ∀ j,nativeState A f payload x K j=
      OriginalSparseNativeProgram.execute Q generators f (extendData x) phaseAt incomingAt K (encodeRole j))
    (out : List (ℕ×ℚ)) (hd : ((decodeInputs Q K out).map Prod.fst).Nodup)
    (hb : ∀ p∈out,p.1<Q+K) (q : Sky (Fin n) f) :
    (∑ j,(lookupCoeff (decodeInputs Q K out) j:ℂ)*nativeState A f payload x K j q)=
      OriginalSparseNativeProgram.output Q K generators f (extendData x) phaseAt incomingAt out q := by
  rw [decoded_gather Q K out hd]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [congr_fun (hstate (decodeRole Q K p.1)) q,encode_decode Q K p.1 (hb p hp)]

end
end FourierSchur.OriginalNativeSparseExecutionBridge
