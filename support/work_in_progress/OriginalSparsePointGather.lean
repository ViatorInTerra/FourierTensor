import work_in_progress.OriginalNativeBankDAG

/-! The sparse reference lists describe actual rational point passes.
Their interpretation preserves every finite role and pays no operation
through a coefficient oracle. The input lists must have distinct sources.
-/
namespace FourierSchur.OriginalSparsePointGather
open OAI.PowerSaving OAI.PowerSaving.Binary Matrix Finset
noncomputable section

variable {ρ : Type*} [Fintype ρ] [DecidableEq ρ]

def lookupCoeff : List (ρ×ℚ) → ρ → ℚ
  | [],_ => 0
  | (i,c)::rest,j => if j=i then c else lookupCoeff rest j

theorem lookup_not_mem (row : List (ρ×ℚ)) (j : ρ)
    (h : j∉row.map Prod.fst) : lookupCoeff row j=0 := by
  induction row with
  | nil => rfl
  | cons p ps ih =>
    have hn : j≠p.1 := by simpa using fun he => h (by simp [he])
    have ht : j∉ps.map Prod.fst := fun hp => h (by simp [hp])
    simp only [lookupCoeff,if_neg hn]
    exact ih ht

theorem sum_lookup (row : List (ρ×ℚ)) (h : (row.map Prod.fst).Nodup) (x : ρ → ℂ) :
    (∑ j,(lookupCoeff row j:ℂ)*x j)=(row.map (fun p => (p.2:ℂ)*x p.1)).sum := by
  induction row with
  | nil => simp [lookupCoeff]
  | cons p ps ih =>
    have hd := List.nodup_cons.mp h
    have hz : lookupCoeff ps p.1=0 := lookup_not_mem ps p.1 hd.1
    have he (j : ρ) : (lookupCoeff (p::ps) j:ℂ)*x j=
        (if j=p.1 then (p.2:ℂ)*x j else 0)+(lookupCoeff ps j:ℂ)*x j := by
      by_cases hj : j=p.1
      · subst j
        simp [lookupCoeff,hz]
      · simp [lookupCoeff,hj]
    simp_rw [he]
    rw [Finset.sum_add_distrib,ih hd.2]
    simp

def encodeRole {Q K : ℕ} : Fin Q⊕Fin K → ℕ
  | .inl i => i.val
  | .inr i => Q+i.val

def decodeRole (Q K : ℕ) [NeZero K] (i : ℕ) : Fin Q⊕Fin K :=
  if h : i<Q then .inl ⟨i,h⟩ else .inr ⟨(i-Q)%K,Nat.mod_lt _ (NeZero.pos K)⟩

theorem decode_encode (Q K : ℕ) [NeZero K] (i : Fin Q⊕Fin K) :
    decodeRole Q K (encodeRole i)=i := by
  cases i with
  | inl i => simp [encodeRole,decodeRole,i.isLt]
  | inr i =>
    have hn : ¬Q+i.val<Q := by omega
    simp [encodeRole,decodeRole,hn,Nat.mod_eq_of_lt i.isLt]

theorem encode_decode (Q K : ℕ) [NeZero K] (i : ℕ) (h : i<Q+K) :
    encodeRole (decodeRole Q K i)=i := by
  by_cases hi : i<Q
  · simp [decodeRole,hi,encodeRole]
  · have hs : i-Q<K := by omega
    simp only [decodeRole,dif_neg hi,encodeRole,Nat.mod_eq_of_lt hs]
    omega

theorem encode_injective (Q K : ℕ) [NeZero K] :
    Function.Injective (encodeRole (Q:=Q) (K:=K)) := by
  intro a b h
  have H := congrArg (decodeRole Q K) h
  simpa only [decode_encode] using H

def decodeInputs (Q K : ℕ) [NeZero K] (row : List (ℕ×ℚ)) : List ((Fin Q⊕Fin K)×ℚ) :=
  row.map (fun p => (decodeRole Q K p.1,p.2))

theorem decoded_gather (Q K : ℕ) [NeZero K] (row : List (ℕ×ℚ))
    (hd : ((decodeInputs Q K row).map Prod.fst).Nodup) (x : (Fin Q⊕Fin K) → ℂ) :
    (∑ j,(lookupCoeff (decodeInputs Q K row) j:ℂ)*x j)=
      (row.map (fun p => (p.2:ℂ)*x (decodeRole Q K p.1))).sum := by
  rw [sum_lookup _ hd]
  simp [decodeInputs,List.map_map,Function.comp_def]

end
end FourierSchur.OriginalSparsePointGather
