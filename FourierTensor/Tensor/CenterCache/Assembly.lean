import work_in_progress.OriginalGroupedCensusBridge
import work_in_progress.OriginalNativeCenterSharing

/-! Embed each invocation and its private workspace in the three-stage network.
The global word consists of those same embedded instructions followed by the
original final frame change, translation and recovery matrix. -/
namespace FourierTensor.CenterCacheAssembly

open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.Cluster Matrix Finset
open FourierSchur FourierSchur.OriginalGroupedFrameWords
open FourierSchur.OriginalGroupedCensusBridge FourierSchur.OriginalNativeCenterSharing
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

abbrev Scratch := (j : J) × (Other j × Free)
abbrev BankRole := Role ⊕ Scratch

def bankBasis : BankRole → OBase Blocks :=
  Sum.elim bases (fun s => basisBox s.1 (axes s.1 s.2.1) (bc (.inl ())))

def bankBorder (n : ℕ) : BankRole → Mask := Sum.elim (border n) (fun _ => ∅)

def bankPosition (j : J) (p : Other j) : (Box ⊕ Free) ↪ BankRole where
  toFun := Sum.elim (fun b => .inl (position j p b)) (fun k => .inr ⟨j,p,k⟩)
  inj' := by
    rintro (b|k) (d|l) h
    · exact congrArg Sum.inl ((position j p).injective (Sum.inl.inj h))
    · cases h
    · cases h
    · simpa using h

set_option linter.constructorNameAsVariable false in
private theorem disjoint_positions (j : J) (p q : Other j) (hpq : p≠q)
    (r : BankRole) (hp : r ∈ covered (bankPosition j p)) :
    r ∉ covered (bankPosition j q) := by
  rw [cover_iff] at hp ⊢
  obtain ⟨(b|k),rfl⟩ := hp
  · rintro ⟨(d|l),hl⟩
    · exact hpq (world_inj j q p d b (Sum.inl.inj hl)).1.symm
    · cases hl
  · rintro ⟨(d|l),hl⟩
    · cases hl
    · change Sum.inr (Sigma.mk j (q,l)) = (Sum.inr (Sigma.mk j (p,k)) : BankRole) at hl
      have h : (q,l) = (p,k) := by simpa only [Sigma.mk.inj_iff, heq_eq_eq,
        true_and, and_self] using Sum.inr.inj hl
      exact hpq (congrArg Prod.fst h).symm

def stageMap (rev : Bool) (j : J) (x : BankRole → ℂ) : BankRole → ℂ :=
  Sum.elim (stageOp rev (x ∘ Sum.inl))
    (fun s => if s.1=j then 0 else x (.inr s))

abbrev LocalCost := J → (ℕ → ℝ) → ℝ

def LocalWords (price : LocalCost) : Prop :=
  ∀ j F (rev : Bool), CPath
    (Sum.elim (basisBox j F) (fun _ : Free => basisBox j F (bc (.inl ()))))
    (Sum.elim (bp j) (fun _ : Free => ∅)) (Sum.elim (bend j) (fun _ : Free => ∅))
    (fun x => Sum.elim ((if rev then OriginalGroupedPricedSharedNetwork.backward
      else OriginalGroupedPricedSharedNetwork.forward) (x ∘ Sum.inl)) (fun _ : Free => 0))
    (price j)

theorem stage {price : LocalCost} (localWords : LocalWords price) (rev : Bool) (j : J) :
    CPath bankBasis (bankBorder j.val) (bankBorder (j.val+1)) (stageMap rev j)
      (fun c => (Fintype.card (Other j):ℝ)*price j c) := by
  let h := fun _ : Other j => fun (x : Box ⊕ Free → ℂ) =>
    Sum.elim ((if rev then OriginalGroupedPricedSharedNetwork.backward
      else OriginalGroupedPricedSharedNetwork.forward) (x ∘ Sum.inl)) (fun _ : Free => 0)
  have hc : (fun c => (Fintype.card (Other j):ℝ)*price j c) =
      (fun c => ∑ _ : Other j, price j c) := by
    funext c; rw [sum_const,card_univ,nsmul_eq_mul]
  rw [hc]
  apply CPath.parallel (bankPosition j) (disjoint_positions j) bankBasis (h:=h)
  · intro p
    have ha : bankBasis ∘ bankPosition j p =
        Sum.elim (basisBox j (axes j p)) (fun _ : Free =>
          basisBox j (axes j p) (bc (.inl ()))) := by
      funext r; cases r with
      | inl r => exact congrFun (bases_local j p) r
      | inr k => rfl
    have hb : bankBorder j.val ∘ bankPosition j p =
        Sum.elim (bp j) (fun _ : Free => ∅) := by
      funext r; cases r with
      | inl r => exact congrFun (border_bp j p) r
      | inr k => rfl
    have he : bankBorder (j.val+1) ∘ bankPosition j p =
        Sum.elim (bend j) (fun _ : Free => ∅) := by
      funext r; cases r with
      | inl r => exact congrFun (border_end j p) r
      | inr k => rfl
    rw [ha,hb,he]
    exact localWords j (axes j p) rev
  · intro p x
    funext r
    rcases r with (((r|r)|(r|r))|k)
    all_goals first | (cases rev <;> rfl) | simp [stageMap,bankPosition,h]
  · intro x r hr
    rcases r with (((k|k)|a)|⟨i,p,k⟩)
    · exfalso; apply hr (omitJ j k); rw [cover_iff]
      exact ⟨Sum.inl (bx (k j)), congrArg Sum.inl (congrArg gx (locate_omit j k))⟩
    · exfalso; apply hr (omitJ j k); rw [cover_iff]
      exact ⟨Sum.inl (byy (k j)), congrArg Sum.inl (congrArg gy (locate_omit j k))⟩
    · rfl
    · by_cases hi : i=j
      · subst i; exfalso; apply hr p; rw [cover_iff]; exact ⟨Sum.inr k,rfl⟩
      · simp [stageMap,hi]
  · intro r hr
    rcases r with (((k|k)|(⟨i,p,a⟩|r))|s)
    · exfalso; apply hr (omitJ j k); rw [cover_iff]
      exact ⟨Sum.inl (bx (k j)), congrArg Sum.inl (congrArg gx (locate_omit j k))⟩
    · exfalso; apply hr (omitJ j k); rw [cover_iff]
      exact ⟨Sum.inl (byy (k j)), congrArg Sum.inl (congrArg gy (locate_omit j k))⟩
    · by_cases hij : i=j
      · subst i; exfalso; apply hr p; rw [cover_iff]; exact ⟨Sum.inl (Sum.inr a),rfl⟩
      · change (if i.val<j.val then univ else ∅) = (if i.val<j.val+1 then univ else ∅)
        have hne : i.val≠j.val := fun e => hij (Fin.ext e)
        simp only [show (i.val<j.val+1) ↔ (i.val<j.val) from (by omega)]
    · rfl
    · rfl

def totalCost (price : LocalCost) (c : ℕ → ℝ) : ℝ :=
  (Fintype.card (Other (0:J)):ℝ)*price 0 c +
  (Fintype.card (Other (1:J)):ℝ)*price 1 c +
  (Fintype.card (Other (2:J)):ℝ)*price 2 c + frameCost (border 3) sink c

/-- One physical word supplies the stated price and every original terminal,
including helper and padding outputs, for arbitrary complex input banks. -/
theorem complete_word {price : LocalCost} (localWords : LocalWords price) :
    ∃ p : Word Blocks BankRole,
      (∀ c : ℕ → ℝ, c 0=0 → wordCost p c=totalCost price c) ∧
      ∀ f (x : Data Blocks BankRole f) (r : Role),
        walk bankBasis f p x (.inl r)=matAct f (kernel Blocks) (x (.inl r)) := by
  have h := ((stage localWords false 0).trans (stage localWords true 1)).trans
    (stage localWords false 2)
  obtain ⟨p,hp,hs⟩ := h
  let i : Role ↪ BankRole := Function.Embedding.inl
  obtain ⟨q,hq,ht⟩ := CPath.reframe bases (border 3) sink
  let tail : Word Blocks Role := q ++ [.translate correction,.localM recoverM]
  refine ⟨p ++ tail.map (OriginalGroupedFrameWords.Move.over i),?_,?_⟩
  · intro c hc
    rw [wordCost_append,wordCost_over i tail c hc,hp c hc]
    have hz : wordCost ([.translate correction,.localM recoverM] : Word Blocks Role) c = 0 := by
      simp [wordCost,moveCost]
    dsimp only [tail]
    rw [wordCost_append,hq c hc,hz,add_zero]
    rfl
  · intro f x r
    obtain ⟨y,rfl⟩ := framed_surj bankBasis (bankBorder 0) f x
    rw [OriginalGroupedFrameWords.walk_append]
    change (walk bankBasis f _ _ ∘ i) r = _
    have hpsem : walk bankBasis f p (withFrame bankBasis (bankBorder 0) f y) =
        withFrame bankBasis (bankBorder 3) f
          (point f (stageMap false 2 ∘ (stageMap true 1 ∘ stageMap false 0)) y) := hs f y
    rw [OriginalGroupedFrameWords.walk_over,hpsem]
    let v : Data Blocks Role f := y ∘ Sum.inl
    have exchange_left (a : BankRole → ℂ) :
        ((stageMap false 2 ∘ (stageMap true 1 ∘ stageMap false 0)) a) ∘ Sum.inl =
        exchange (a ∘ Sum.inl) := by
      funext z
      rcases z with (k|k)|a <;> simp [Function.comp_def,stageMap,stageOp,exchange,gx,gy]
    have hIn :
        (withFrame bankBasis (bankBorder 3) f
          (point f (stageMap false 2 ∘ (stageMap true 1 ∘ stageMap false 0)) y)) ∘ i =
        withFrame bases (border 3) f (point f exchange v) := by
      funext r
      apply congrArg (matAct f (frame (bases r) (border 3 r)))
      funext a
      exact congrFun (exchange_left (fun k => y k a)) r
    change walk bases f tail _ r = matAct f (kernel Blocks) (withFrame bases (border 0) f v r)
    rw [hIn]
    unfold tail
    rw [OriginalGroupedFrameWords.walk_append,ht]
    simp only [OriginalGroupedFrameWords.walk,List.foldl_cons,List.foldl_nil,OriginalGroupedFrameWords.Move.go,recover_eq]
    exact congrFun (netEffect f v) r

end
end FourierTensor.CenterCacheAssembly
