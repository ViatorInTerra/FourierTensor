import work_in_progress.OriginalGroupedFrameCompilerRAM

/-!
Localized sharing of a generated coefficient image.  Original roles and
fresh scratch have different tags.  Only scratch receives recursive frame
requests; all original roles remain live.  The three-token word compiles
through the existing native RAM sweep, including initialization, rational
coefficient preparation, all point arithmetic, gathers and routing.

This is a local executor, not a sparsity theorem for its repeated use.
-/
namespace FourierSchur.OriginalLocalizedBankSharing
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty Matrix Finset
open OriginalGroupedFrameWords OriginalGroupedWordRAM
open scoped BigOperators
noncomputable section

variable {α η κ : Type*} [Fintype α] [DecidableEq α]
  [Fintype η] [DecidableEq η] [Fintype κ] [DecidableEq κ]

def gatherMatrix (B : Matrix κ η ℚ) : Matrix (η ⊕ κ) (η ⊕ κ) ℚ :=
  Matrix.fromBlocks 1 0 B 0

def consumeMatrix (D : Matrix η κ ℚ) : Matrix (η ⊕ κ) (η ⊕ κ) ℚ :=
  Matrix.fromBlocks 1 D 0 0

def scratchMask (S : Finset α) : η ⊕ κ → Finset α
  | .inl _ => ∅
  | .inr _ => S

def sharedWord (B : Matrix κ η ℚ) (D : Matrix η κ ℚ) (S : Finset α) :
    OriginalGroupedFrameWords.Word α (η ⊕ κ) :=
  [.localM (gatherMatrix B), .frames (fun _ => ∅) (scratchMask S),
    .localM (consumeMatrix D)]

/-- Both frame directions are native requests. In particular S→∅
executes the inverse frame, including its paid translation correction. -/
def sharedRatioWord (B : Matrix κ η ℚ) (D : Matrix η κ ℚ) (S T : Finset α) :
    OriginalGroupedFrameWords.Word α (η ⊕ κ) :=
  [.localM (gatherMatrix B), .frames (scratchMask S) (scratchMask T),
    .localM (consumeMatrix D)]

private theorem cast_indicator (P : Prop) [Decidable P] :
    (((if P then 1 else 0):ℚ):ℂ)=if P then 1 else 0 := by
  split <;> norm_num

private theorem unframe_empty (A : OBase α) : unframe A ∅=1 := by
  simp [unframe,OBase.proj,wrap_one]

omit [DecidableEq κ] in
/-- The generated inputs are formed by paid scalar operations. Scratch
contents on entry are irrelevant; no original input role is overwritten. -/
theorem gather_original (B : Matrix κ η ℚ) (x : (η ⊕ κ) → ℂ) (j : η) :
    actPoint (gatherMatrix B) x (.inl j)=x (.inl j) := by
  simp [actPoint,gatherMatrix,Fintype.sum_sum_type,Matrix.one_apply,
    cast_indicator,ite_mul]

omit [DecidableEq κ] in
theorem gather_scratch (B : Matrix κ η ℚ) (x : (η ⊕ κ) → ℂ) (k : κ) :
    actPoint (gatherMatrix B) x (.inr k)=∑ j, (B k j:ℂ)*x (.inl j) := by
  simp [actPoint,gatherMatrix,Fintype.sum_sum_type]

omit [DecidableEq κ] in
theorem consume_original (D : Matrix η κ ℚ) (x : (η ⊕ κ) → ℂ) (j : η) :
    actPoint (consumeMatrix D) x (.inl j)=
      x (.inl j)+∑ k, (D j k:ℂ)*x (.inr k) := by
  simp [actPoint,consumeMatrix,Fintype.sum_sum_type,Matrix.one_apply,
    cast_indicator,ite_mul]

omit [DecidableEq κ] in
theorem consume_scratch (D : Matrix η κ ℚ) (x : (η ⊕ κ) → ℂ) (k : κ) :
    actPoint (consumeMatrix D) x (.inr k)=0 := by
  simp [actPoint,consumeMatrix,Fintype.sum_sum_type]

omit [DecidableEq κ] in
/-- The exact output retains every original independent input and adds
the shared generated correction. Scratch is reset by a paid point pass. -/
theorem sharedWord_correct (A : (η ⊕ κ) → OBase α)
    (B : Matrix κ η ℚ) (D : Matrix η κ ℚ) (S : Finset α)
    (f : ℕ) (x : Data α (η ⊕ κ) f) (j : η) (q : Sky α f) :
    OriginalGroupedFrameWords.walk A f (sharedWord B D S) x (.inl j) q=
      x (.inl j) q+∑ k, (D j k:ℂ)*
        matAct f (frame (A (.inr k)) S)
          (fun z => ∑ i, (B k i:ℂ)*x (.inl i) z) q := by
  have hs (k : κ) : point f (actPoint (gatherMatrix B)) x (.inr k)=
      (fun z => ∑ i, (B k i:ℂ)*x (.inl i) z) := by
    funext z
    exact gather_scratch B _ k
  simp only [sharedWord,OriginalGroupedFrameWords.walk,List.foldl_cons,List.foldl_nil,
    OriginalGroupedFrameWords.Move.go,point,consume_original,multiAct,scratchMask]
  simp only [unframe_empty,frame_zero,Matrix.mul_one,matAct_one,
    hs,point,gather_original]

omit [DecidableEq κ] in
theorem sharedWord_scratch_zero (A : (η ⊕ κ) → OBase α)
    (B : Matrix κ η ℚ) (D : Matrix η κ ℚ) (S : Finset α)
    (f : ℕ) (x : Data α (η ⊕ κ) f) (k : κ) :
    OriginalGroupedFrameWords.walk A f (sharedWord B D S) x (.inr k)=0 := by
  funext q
  exact consume_scratch D _ k

omit [DecidableEq κ] in
theorem sharedRatioWord_correct (A : (η ⊕ κ) → OBase α)
    (B : Matrix κ η ℚ) (D : Matrix η κ ℚ) (S T : Finset α)
    (f : ℕ) (x : Data α (η ⊕ κ) f) (j : η) (q : Sky α f) :
    OriginalGroupedFrameWords.walk A f (sharedRatioWord B D S T) x (.inl j) q=
      x (.inl j) q+∑ k, (D j k:ℂ)*
        matAct f (frame (A (.inr k)) T * unframe (A (.inr k)) S)
          (fun z => ∑ i, (B k i:ℂ)*x (.inl i) z) q := by
  have hs (k : κ) : point f (actPoint (gatherMatrix B)) x (.inr k)=
      (fun z => ∑ i, (B k i:ℂ)*x (.inl i) z) := by
    funext z
    exact gather_scratch B _ k
  simp only [sharedRatioWord,OriginalGroupedFrameWords.walk,List.foldl_cons,
    List.foldl_nil,OriginalGroupedFrameWords.Move.go,point,consume_original,
    multiAct,scratchMask]
  simp only [unframe_empty,frame_zero,Matrix.mul_one,matAct_one,
    hs,point,gather_original]

omit [DecidableEq κ] in
theorem sharedRatioWord_preserves (A : (η ⊕ κ) → OBase α)
    (B : Matrix κ η ℚ) (D : Matrix η κ ℚ) (S T : Finset α)
    (j : η) (hj : ∀ k, D j k=0) (f : ℕ) (x : Data α (η ⊕ κ) f) :
    OriginalGroupedFrameWords.walk A f (sharedRatioWord B D S T) x (.inl j)=x (.inl j) := by
  funext q
  rw [sharedRatioWord_correct]
  simp [hj]

omit [DecidableEq κ] in
/-- Any untouched original auxiliary bank is preserved on arbitrary
complex input, even when fresh scratch initially contains arbitrary data. -/
theorem sharedWord_preserves (A : (η ⊕ κ) → OBase α)
    (B : Matrix κ η ℚ) (D : Matrix η κ ℚ) (S : Finset α)
    (j : η) (hj : ∀ k, D j k=0) (f : ℕ) (x : Data α (η ⊕ κ) f) :
    OriginalGroupedFrameWords.walk A f (sharedWord B D S) x (.inl j)=x (.inl j) := by
  funext q
  rw [sharedWord_correct]
  simp [hj]

omit [Fintype α] [DecidableEq κ] in
/-- Every retained spectator fiber is included. Only the fresh κ rows
receive child calls; coefficient sizes do not discount those calls. -/
theorem sharedWord_charge (X : Layout α) (r f : ℕ) (tau : ℕ → ℕ)
    (B : Matrix κ η ℚ) (D : Matrix η κ ℚ) (S : Finset α) :
    wordCharge X r f tau (sharedWord B D S)=
      Fintype.card κ * (if S.card=0 then 0 else
        (2^r*(2^f)^(X.n-S.card))*tau (S.card*f)) := by
  simp [sharedWord,wordCharge,moveCharge,frameCharge,residualRank,
    scratchMask,Fintype.sum_sum_type]

omit [Fintype α] [DecidableEq κ] in
theorem sharedRatioWord_charge (X : Layout α) (r f : ℕ) (tau : ℕ → ℕ)
    (B : Matrix κ η ℚ) (D : Matrix η κ ℚ) (S T : Finset α) :
    wordCharge X r f tau (sharedRatioWord B D S T)=
      Fintype.card κ * (if ((S\T) ∪ (T\S)).card=0 then 0 else
        (2^r*(2^f)^(X.n-((S\T) ∪ (T\S)).card))*tau (((S\T) ∪ (T\S)).card*f)) := by
  simp [sharedRatioWord,wordCharge,moveCharge,frameCharge,residualRank,
    scratchMask,Fintype.sum_sum_type]

section RAM
universe U
variable {ι : Type U} {m : Bool} {cl : Paint} {f : ι → ℕ}
  {s : Ty} {x : ι → T s} {X : Layout α} {R : Layout (η ⊕ κ)} {r : ℕ}
  {v : ∀ i, Grain α (η ⊕ κ) r (f i)}

/-- Actual open native code for the localized sharing word. The callback
contract is the same raw complete-kernel contract as the enclosing native
recursion. All other operations are implemented by existing RAM code;
the additive child price is not multiplied by the local constant. -/
theorem sharedWord_native (b : Bank (hatch cl) ι)
    (h : Rig m b.B f s x cl X R r v) (hr : 3≤X.n)
    (A : (η ⊕ κ) → OBase α) (tau : ι → ℕ → ℕ)
    (HC : ∀ n : ℕ, 0<n → n≤X.n → GroupedResidual.Rig.RawContract cl b
      (fun i => n*f i) (fun i => tau i (n*f i)))
    (B : Matrix κ η ℚ) (D : Matrix η κ ℚ) (S : Finset α) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape
        (coastline A r (f i) (sharedWord B D S) (v i)))
      (fun i => (fleet X R r (f i)).n)
      (fun i => Fintype.card κ * (if S.card=0 then 0 else
        (2^r*(2^f i)^(X.n-S.card))*tau i (S.card*f i))) := by
  have HF := OriginalGroupedFrameCompilerRAM.frame_service cl m X R r hr f A b tau HC
  have H := sweep A b tau HF h (sharedWord B D S)
  simpa only [sharedWord_charge] using H

theorem sharedRatioWord_native (b : Bank (hatch cl) ι)
    (h : Rig m b.B f s x cl X R r v) (hr : 3≤X.n)
    (A : (η ⊕ κ) → OBase α) (tau : ι → ℕ → ℕ)
    (HC : ∀ n : ℕ, 0<n → n≤X.n → GroupedResidual.Rig.RawContract cl b
      (fun i => n*f i) (fun i => tau i (n*f i)))
    (B : Matrix κ η ℚ) (D : Matrix η κ ℚ) (S T : Finset α) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape
        (coastline A r (f i) (sharedRatioWord B D S T) (v i)))
      (fun i => (fleet X R r (f i)).n)
      (fun i => Fintype.card κ * (if ((S\T) ∪ (T\S)).card=0 then 0 else
        (2^r*(2^f i)^(X.n-((S\T) ∪ (T\S)).card))*tau i (((S\T) ∪ (T\S)).card*f i))) := by
  have HF := OriginalGroupedFrameCompilerRAM.frame_service cl m X R r hr f A b tau HC
  have H := sweep A b tau HF h (sharedRatioWord B D S T)
  simpa only [sharedRatioWord_charge] using H
end RAM

end
end FourierSchur.OriginalLocalizedBankSharing
