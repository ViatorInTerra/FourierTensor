import work_in_progress.OriginalGroupedMaskCards
import work_in_progress.OriginalGroupedNeighborCount

/-! Native grouped inventory from actual mask ranks and native role types.
This establishes the finite geometry independently of a particular emitted
RAM word. Matching its occurrences to the grouped compiler remains a program
construction obligation. -/

namespace FourierSchur.OriginalGroupedNativeInventory
open OAI.PowerSaving OAI.PowerSaving.Cluster Finset
open OriginalGroupedResidualCertificate OriginalGroupedMaskCards OriginalGroupedNeighborCount
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000

theorem card_center : Fintype.card Center=33 := by
  norm_num [Fintype.card_sum]

def Active : Role → Prop
  | .inl _ => True
  | .inr (.inl ⟨_,_,.inl s⟩) => neighbor s.1 s.2
  | .inr (.inl ⟨_,_,.inr _⟩) => True
  | .inr (.inr _) => False

instance activeDec : DecidablePred Active := by
  intro r
  rcases r with a|a
  · exact isTrue trivial
  · rcases a with ⟨j,p,a⟩|s
    · rcases a with a|a
      · exact inferInstanceAs (Decidable (neighbor a.1 a.2))
      · exact isTrue trivial
    · exact isFalse id

abbrev ActiveType := Across ⊕ (Σ j : J, Other j × (NeighborSide ⊕ Center))

def activeEquiv : {r : Role // Active r} ≃ ActiveType where
  toFun := by
    rintro ⟨r,hr⟩
    rcases r with a|a
    · exact .inl a
    · rcases a with ⟨j,p,a⟩|s
      · rcases a with a|a
        · exact .inr ⟨j,p,.inl ⟨a,hr⟩⟩
        · exact .inr ⟨j,p,.inr a⟩
      · exact False.elim hr
  invFun := by
    intro r
    rcases r with a|⟨j,p,a⟩
    · exact ⟨.inl a,trivial⟩
    · rcases a with ⟨a,ha⟩|a
      · exact ⟨gu j p (.inl a),ha⟩
      · exact ⟨gu j p (.inr a),trivial⟩
  left_inv := by
    rintro ⟨r,hr⟩
    rcases r with a|a
    · rfl
    · rcases a with ⟨j,p,a⟩|s
      · rcases a with a|a <;> rfl
      · exact False.elim hr
  right_inv := by
    intro r
    rcases r with a|⟨j,p,a⟩
    · rfl
    · rcases a with a|a <;> rfl

theorem active_roles_card : Fintype.card {r : Role // Active r}=roles32 := by
  rw [Fintype.card_congr activeEquiv]
  simp only [ActiveType,Fintype.card_sum,card_key,Fintype.card_sigma,
    Fintype.card_prod,card_other,neighbor_side_card]
  norm_num [Fin.sum_univ_succ,roles32]

theorem inactive_roles_card :
    Fintype.card {r : Role // ¬Active r}=522249062646224 := by
  rw [Fintype.card_subtype_compl,card_role,active_roles_card]
  norm_num [tower,roles32]

/-- Actual role type cardinalities for the ten retained edge families.
The three center changes of order h have separate charged occurrences. -/
def nativeEdgeCount (j : J) : Fin 10 → ℕ :=
  let banks := 2*Fintype.card Key
  let centers := Fintype.card (Other j × Center)
  let sides := Fintype.card (Other j × NeighborSide)
  ![banks,banks,centers,3*centers,centers,sides,sides,sides,sides,sides]

theorem nativeEdgeCount_eq (j : J) (i : Fin 10) :
    nativeEdgeCount j i=edgeCount 32 4060 3006 i := by
  fin_cases i <;> simp only [nativeEdgeCount,Fintype.card_prod,
    card_key,card_other,card_center,neighbor_side_card] <;> norm_num [edgeCount]

def nativeHistogram (rank : ℕ) : ℕ :=
  ∑ j : J, ∑ i : Fin 10,
    if stageRanks j i=rank then nativeEdgeCount j i else 0

theorem nativeHistogram_eq (rank : ℕ) : nativeHistogram rank=histogram 32 4060 3006 rank := by
  unfold nativeHistogram histogram
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [stageRanks_eq,nativeEdgeCount_eq]

theorem nativeHistogram32 (i : Fin 12) : nativeHistogram (rho32 i)=count32 i := by
  rw [nativeHistogram_eq]
  exact histogram32 i

theorem stageRank_covers (j : J) (i : Fin 10) :
    stageRanks j i=0 ∨ ∃ k : Fin 12, stageRanks j i=rho32 k := by
  rw [stageRanks_eq]
  fin_cases j <;> fin_cases i <;> decide

theorem rho32_injective : Function.Injective rho32 := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num [rho32] at h <;> rfl

theorem native_full_first_moment :
    (∑ i : Fin 12, nativeHistogram (rho32 i)*rho32 i)+
      Fintype.card {r : Role // ¬Active r}*order32+saving32=padded32*order32 := by
  simp only [nativeHistogram32,inactive_roles_card]
  norm_num [count32,rho32,order32,saving32,padded32,Fin.sum_univ_succ]

def nativePaddedMoment (z : ℝ) : ℝ :=
  (Fintype.card {r : Role // ¬Active r}:ℝ)/(Fintype.card Role:ℝ)+
    ∑ i : Fin 12, (nativeHistogram (rho32 i):ℝ)/(Fintype.card Role:ℝ)*
      ((rho32 i:ℝ)/(Fintype.card Blocks:ℝ))^z

theorem nativePaddedMoment_eq (z : ℝ) : nativePaddedMoment z=paddedMoment32 z := by
  unfold nativePaddedMoment paddedMoment32 moment
  simp only [inactive_roles_card,card_role,nativeHistogram32,card_blocks]
  rfl

theorem nativePaddedMoment_alpha32_lt : nativePaddedMoment alpha32<1 := by
  rw [nativePaddedMoment_eq]
  exact paddedMoment32_alpha32_lt

theorem nativePaddedMoment_alphaG_lt : nativePaddedMoment alphaG<1 := by
  rw [nativePaddedMoment_eq]
  exact paddedMoment32_alphaG_lt

theorem nativePaddedMoment_zero_gt_one : 1<nativePaddedMoment 0 := by
  rw [nativePaddedMoment_eq]
  exact zero_moments_gt_one.2

end
end FourierSchur.OriginalGroupedNativeInventory
