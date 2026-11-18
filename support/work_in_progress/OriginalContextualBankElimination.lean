import work_in_progress.OriginalLocalizedBankWorkspaceRAM
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
Two-sided elimination of common-operator banks. Both the input map B and
the complete future consumer map L are part of the certificate. A factor
L * B = D * E replaces the whole sandwich, including when B itself has
independent rows. No auxiliary output may be omitted from L.

The replacement uses the existing paid native generated-bank word with
scratch indexed by the factor dimension. This file proves the local
compilation rule, not a new global contraction profile.
-/
namespace FourierSchur.OriginalContextualBankElimination
open Matrix
open scoped Kronecker
noncomputable section

section Matrices
variable {ι κ ν ο σ : Type*}
  [Fintype ι] [Fintype κ] [Fintype ν] [Fintype ο] [Fintype σ]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]
  [DecidableEq ο] [DecidableEq σ]

/-- Complete input, operator, and consumer maps on all physical lanes. -/
def sandwich (L : Matrix ο κ ℂ) (A : Matrix σ σ ℂ) (B : Matrix κ ι ℂ) :
    Matrix (ο × σ) (ι × σ) ℂ :=
  (L ⊗ₖ (1 : Matrix σ σ ℂ)) *
    ((1 : Matrix κ κ ℂ) ⊗ₖ A) * (B ⊗ₖ (1 : Matrix σ σ ℂ))

theorem sandwich_eq (L : Matrix ο κ ℂ) (A : Matrix σ σ ℂ)
    (B : Matrix κ ι ℂ) : sandwich L A B = (L*B) ⊗ₖ A := by
  simp only [sandwich, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

/-- The factor dimension may be smaller than the row rank of B: directions
annihilated by the complete consumer do not receive physical kernel calls. -/
theorem eliminate (L : Matrix ο κ ℂ) (B : Matrix κ ι ℂ)
    (D : Matrix ο ν ℂ) (E : Matrix ν ι ℂ) (A : Matrix σ σ ℂ)
    (h : L*B=D*E) : sandwich L A B = sandwich D A E := by
  rw [sandwich_eq, sandwich_eq, h]

/-- Every output coordinate is preserved for arbitrary independent complex
input coordinates. No symmetry, zero-input, or norm hypothesis is used. -/
theorem eliminate_apply (L : Matrix ο κ ℂ) (B : Matrix κ ι ℂ)
    (D : Matrix ο ν ℂ) (E : Matrix ν ι ℂ) (A : Matrix σ σ ℂ)
    (h : L*B=D*E) (x : ι × σ → ℂ) (o : ο × σ) :
    (sandwich L A B).mulVec x o = (sandwich D A E).mulVec x o := by
  rw [eliminate L B D E A h]

end Matrices

section ThreeStages
variable {η σ κ₀ κ₁ κ₂ ν₀ ν₁ ν₂ : Type*}
  [Fintype η] [Fintype σ]
  [Fintype κ₀] [Fintype κ₁] [Fintype κ₂]
  [Fintype ν₀] [Fintype ν₁] [Fintype ν₂]
  [DecidableEq η] [DecidableEq σ]
  [DecidableEq κ₀] [DecidableEq κ₁] [DecidableEq κ₂]
  [DecidableEq ν₀] [DecidableEq ν₁] [DecidableEq ν₂]

/-- Each replacement preserves the entire bank vector at its boundary;
therefore the forward, inverse-transpose, forward composition preserves
all original auxiliary outputs as well as the signal outputs. -/
theorem three_stages
    (A₀ A₁ A₂ : Matrix σ σ ℂ)
    (L₀ : Matrix η κ₀ ℂ) (B₀ : Matrix κ₀ η ℂ)
    (L₁ : Matrix η κ₁ ℂ) (B₁ : Matrix κ₁ η ℂ)
    (L₂ : Matrix η κ₂ ℂ) (B₂ : Matrix κ₂ η ℂ)
    (D₀ : Matrix η ν₀ ℂ) (E₀ : Matrix ν₀ η ℂ)
    (D₁ : Matrix η ν₁ ℂ) (E₁ : Matrix ν₁ η ℂ)
    (D₂ : Matrix η ν₂ ℂ) (E₂ : Matrix ν₂ η ℂ)
    (h₀ : L₀*B₀=D₀*E₀) (h₁ : L₁*B₁=D₁*E₁) (h₂ : L₂*B₂=D₂*E₂) :
    sandwich L₂ A₂ B₂ * sandwich L₁ A₁ B₁ * sandwich L₀ A₀ B₀ =
      sandwich D₂ A₂ E₂ * sandwich D₁ A₁ E₁ * sandwich D₀ A₀ E₀ := by
  rw [eliminate L₀ B₀ D₀ E₀ A₀ h₀, eliminate L₁ B₁ D₁ E₁ A₁ h₁,
    eliminate L₂ B₂ D₂ E₂ A₂ h₂]
end ThreeStages

section PaidWord
open OAI.PowerSaving OAI.PowerSaving.Binary
open OriginalGroupedFrameWords OriginalGroupedWordRAM OriginalLocalizedBankSharing
variable {α η ν : Type*} [Fintype α] [DecidableEq α]
  [Fintype η] [DecidableEq η] [Fintype ν] [DecidableEq ν]

/-- The emitted replacement is a paid gather, physical frame conversion,
and consume word. The exact charge retains every spectator repetition. -/
theorem eliminated_word_charge (X : Layout α) (r f : ℕ) (tau : ℕ → ℕ)
    (E : Matrix ν η ℚ) (D : Matrix η ν ℚ) (S T : Finset α) :
    wordCharge X r f tau (sharedRatioWord E D S T)=
      Fintype.card ν * (if ((S\T) ∪ (T\S)).card=0 then 0 else
        (2^r*(2^f)^(X.n-((S\T) ∪ (T\S)).card))*tau (((S\T) ∪ (T\S)).card*f)) :=
  sharedRatioWord_charge X r f tau E D S T

end PaidWord

section TranslatedWord
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty Finset
open OriginalGroupedFrameWords OriginalGroupedWordRAM OriginalLocalizedBankSharing
open OriginalLocalizedBankWorkspaceRAM
variable {α η ν : Type*} [Fintype α] [DecidableEq α]
  [Fintype η] [DecidableEq η] [Fintype ν] [DecidableEq ν]

def scratchShift (z : Space α) : η ⊕ ν → Space α
  | .inl _ => 0
  | .inr _ => z

/-- A phase differing from a native frame ratio by an even linear phase
uses an ordinary paid address translation before its complete consumer. -/
def translatedWord (E : Matrix ν η ℚ) (D : Matrix η ν ℚ)
    (S T : Finset α) (z : Space α) : Word α (η ⊕ ν) :=
  [.localM (gatherMatrix E), .frames (scratchMask S) (scratchMask T),
    .translate (scratchShift z), .localM (consumeMatrix D)]

private theorem empty_unframe (A : OBase α) : unframe A ∅=1 := by
  simp [unframe,OBase.proj,wrap_one]

omit [DecidableEq ν] in
theorem translatedWord_correct (A : (η ⊕ ν) → OBase α)
    (E : Matrix ν η ℚ) (D : Matrix η ν ℚ) (S T : Finset α) (z : Space α)
    (f : ℕ) (x : Data α (η ⊕ ν) f) (j : η) (q : Sky α f) :
    OriginalGroupedFrameWords.walk A f (translatedWord E D S T z) x (.inl j) q=
      x (.inl j) q+∑ k, (D j k:ℂ)*
        matAct f (shift z * (frame (A (.inr k)) T * unframe (A (.inr k)) S))
          (fun w => ∑ i, (E k i:ℂ)*x (.inl i) w) q := by
  have hs (k : ν) : point f (actPoint (gatherMatrix E)) x (.inr k)=
      (fun w => ∑ i, (E k i:ℂ)*x (.inl i) w) := by
    funext w
    exact gather_scratch E _ k
  simp only [translatedWord,OriginalGroupedFrameWords.walk,List.foldl_cons,List.foldl_nil,
    OriginalGroupedFrameWords.Move.go,
    point,consume_original,multiAct,scratchShift,scratchMask]
  simp only [empty_unframe,frame_zero,Matrix.mul_one,matAct_one,
    shift_zero,hs,point,gather_original,matAct_mul]

omit [Fintype α] [DecidableEq ν] in
theorem translatedWord_charge (X : Layout α) (r f : ℕ) (tau : ℕ → ℕ)
    (E : Matrix ν η ℚ) (D : Matrix η ν ℚ) (S T : Finset α) (z : Space α) :
    wordCharge X r f tau (translatedWord E D S T z)=
      Fintype.card ν * (if ((S\T) ∪ (T\S)).card=0 then 0 else
        (2^r*(2^f)^(X.n-((S\T) ∪ (T\S)).card))*tau (((S\T) ∪ (T\S)).card*f)) := by
  simp [translatedWord,wordCharge,moveCharge,frameCharge,residualRank,
    scratchMask,Fintype.sum_sum_type]

section RAM
universe U
variable {ι : Type U} {m : Bool} {cl : Paint} {f : ι → ℕ}
  {s : Ty} {x : ι → T s} {X : Layout α} {R0 : Layout η} {r : ℕ}
  {v : ∀ i, Grain α η r (f i)}

/-- Starts with original input roles only, allocates and initializes all
scratch, executes every local operation and address route, and retains the
exact additive callback bill. The local allowance is original input width. -/
theorem translatedWord_native (b : Bank (hatch cl) ι)
    (h : Rig m b.B f s x cl X R0 r v) (R : Layout (η ⊕ ν)) (j : η)
    (hr : 3≤X.n) (A : (η ⊕ ν) → OBase α) (tau : ι → ℕ → ℕ)
    (HC : ∀ n : ℕ, 0<n → n≤X.n → GroupedResidual.Rig.RawContract cl b
      (fun i => n*f i) (fun i => tau i (n*f i)))
    (E : Matrix ν η ℚ) (D : Matrix η ν ℚ) (S T : Finset α) (z : Space α) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape
        (coastline A r (f i) (translatedWord E D S T z) (padded (v i))))
      (fun i => (fleet X R0 r (f i)).n)
      (fun i => Fintype.card ν * (if ((S\T) ∪ (T\S)).card=0 then 0 else
        (2^r*(2^f i)^(X.n-((S\T) ∪ (T\S)).card))*tau i (((S\T) ∪ (T\S)).card*f i))) := by
  let env i : Ty.T (p s (bundle cl)) :=
    (x i,(fleet X R r (f i)).tape (padded (κ:=ν) (v i)))
  have hg := h.gather id env (t:=p s (bundle cl)) Can.first
  have hp : Rig m b.B f (p s (bundle cl)) env cl X R r
      (fun i => padded (κ:=ν) (v i)) := ⟨hg.gear,hg.imag,Can.second⟩
  have HF := OriginalGroupedFrameCompilerRAM.frame_service cl m X R r hr f A b tau HC
  have HS := sweep A b tau HF hp (translatedWord E D S T z)
  have H := (Able.of_can (b:=b) (prepare_scratch h R)).save_keep HS
  have H' : Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape
        (coastline A r (f i) (translatedWord E D S T z) (padded (v i))))
      (fun i => (fleet X R r (f i)).n)
      (fun i => Fintype.card ν * (if ((S\T) ∪ (T\S)).card=0 then 0 else
        (2^r*(2^f i)^(X.n-((S\T) ∪ (T\S)).card))*tau i (((S\T) ∪ (T\S)).card*f i))) := by
    simpa only [Nat.zero_add,translatedWord_charge] using H
  apply H'.weaken ?_ (fun _ => Nat.le_refl _)
  refine ⟨R.n+1,fun i => ?_⟩
  have hw := workspace_width (X:=X) (R0:=R0) (r:=r) R j (f i)
  dsimp
  nlinarith

end RAM
end TranslatedWord
end
end FourierSchur.OriginalContextualBankElimination
