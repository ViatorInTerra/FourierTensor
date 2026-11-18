import work_in_progress.OriginalSparseNativeRows

/-! Acyclic sparse-program certificate soundness at every amplification.
All original inputs are arbitrary complex arrays. A symbolic row is an
algebraic proof object; it is not a coefficient oracle for execution.
-/
namespace FourierSchur.OriginalSparseNativeProgram
open OAI.PowerSaving OAI.PowerSaving.Binary Matrix Finset
open OriginalNativeGeneratorSymbols OriginalSparseNativeRows
noncomputable section

variable {n k : ℕ}

def execute (Q : ℕ) (generators : Fin k → Space (Fin n) → ℂ) (f : ℕ)
    (x : ℕ → Sky (Fin n) f → ℂ) (phaseAt : ℕ → Tag)
    (incomingAt : ℕ → List (ℕ×ℚ)) : ℕ → ℕ → Sky (Fin n) f → ℂ
  | 0 => x
  | t+1 => Function.update (execute Q generators f x phaseAt incomingAt t) (Q+t)
      (matAct f (operator generators (phaseAt t)) (fun q =>
        ((incomingAt t).map (fun p => (p.2:ℂ)*
          execute Q generators f x phaseAt incomingAt t p.1 q)).sum))

theorem act_inputRow (generators : Fin k → Space (Fin n) → ℂ)
    (f : ℕ) (x : ℕ → Sky (Fin n) f → ℂ) (i : ℕ) :
    act generators f x [⟨i,unitTag,1⟩]=x i := by
  have ho : operator generators unitTag=1 := by
    rw [operator]
    have hv : value generators unitTag=fun _ => 1 := funext (value_unit generators)
    rw [hv,wrap_one]
  funext q
  simp [OriginalSparseNativeRows.act,mean,ho]

/-- Exact row certificates and causal references imply the complete
physical data identity, without enumerating input arrays or frequencies. -/
theorem execute_rows (Q K : ℕ) (directions : Fin k → ℕ)
    (generators : Fin k → Space (Fin n) → ℂ)
    (hs : ∀ i x,generators i x*generators i x=character n (directions i) x)
    (f : ℕ) (x : ℕ → Sky (Fin n) f → ℂ)
    (phaseAt : ℕ → Tag) (incomingAt : ℕ → List (ℕ×ℚ)) (rowAt : ℕ → Row)
    (hinit : ∀ i,Q>i → rowAt i=[⟨i,unitTag,1⟩])
    (hcausal : ∀ t,t<K → ∀ p∈incomingAt t,p.1<Q+t)
    (hrows : ∀ t,t<K → nextRow directions (phaseAt t) rowAt (incomingAt t)=rowAt (Q+t)) :
    ∀ t,t≤K → ∀ j,j<Q+t →
      execute Q generators f x phaseAt incomingAt t j=act generators f x (rowAt j) := by
  intro t
  induction t with
  | zero =>
    intro _ j hj
    rw [hinit j (by simpa using hj),act_inputRow]
    rfl
  | succ t ih =>
    intro ht j hj
    have htk : t<K := by omega
    by_cases hje : j=Q+t
    · subst j
      rw [execute,Function.update_self,← hrows t htk,
        act_nextRow directions generators hs]
      congr 1
      funext q
      apply congrArg List.sum
      apply List.map_congr_left
      intro p hp
      rw [congr_fun (ih (by omega) p.1 (hcausal t htk p hp)) q]
    · rw [execute,Function.update_of_ne hje]
      exact ih (by omega) j (by omega)

def output (Q K : ℕ) (generators : Fin k → Space (Fin n) → ℂ) (f : ℕ)
    (x : ℕ → Sky (Fin n) f → ℂ) (phaseAt : ℕ → Tag)
    (incomingAt : ℕ → List (ℕ×ℚ)) (out : List (ℕ×ℚ)) : Sky (Fin n) f → ℂ :=
  fun q => (out.map (fun p => (p.2:ℂ)*
    execute Q generators f x phaseAt incomingAt K p.1 q)).sum

theorem output_rows (Q K : ℕ) (directions : Fin k → ℕ)
    (generators : Fin k → Space (Fin n) → ℂ)
    (hs : ∀ i x,generators i x*generators i x=character n (directions i) x)
    (f : ℕ) (x : ℕ → Sky (Fin n) f → ℂ)
    (phaseAt : ℕ → Tag) (incomingAt : ℕ → List (ℕ×ℚ)) (rowAt : ℕ → Row)
    (hinit : ∀ i,Q>i → rowAt i=[⟨i,unitTag,1⟩])
    (hcausal : ∀ t,t<K → ∀ p∈incomingAt t,p.1<Q+t)
    (hrows : ∀ t,t<K → nextRow directions (phaseAt t) rowAt (incomingAt t)=rowAt (Q+t))
    (out : List (ℕ×ℚ)) (hout : ∀ p∈out,p.1<Q+K) (target : Row)
    (hcheck : normalize (gather rowAt out)=target) :
    output Q K generators f x phaseAt incomingAt out=act generators f x target := by
  rw [← hcheck,act_normalize,act_gather]
  funext q
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [congr_fun (execute_rows Q K directions generators hs f x phaseAt incomingAt rowAt
    hinit hcausal hrows K (by omega) p.1 (hout p hp)) q]

end
end FourierSchur.OriginalSparseNativeProgram
