import work_in_progress.OriginalContextualBankElimination

/-!
Joint translated-bank factorization with an actual native RAM word.

All translated gathers precede ONE common frame-service batch. Every
translated consumer follows it. Original roles, including arbitrary original
auxiliaries, stay live; only separately tagged fresh scratch is cleared.
Translation-polynomial coefficients are finite fixed program parameters.
Their preparation and every point pass and route are paid by the native
word compiler. No Fourier conversion or restricted-sector service is used.

This is the execution bridge for a supplied exact bank factorization. It
does not assert a new factorization or a contracted whole-network inventory.
-/
namespace FourierSchur.OriginalTranslatedBankPolynomialRAM
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty Matrix Finset
open OriginalGroupedFrameWords OriginalGroupedWordRAM OriginalLocalizedBankSharing
open OriginalLocalizedBankWorkspaceRAM
open scoped BigOperators
noncomputable section

variable {α η κ : Type*} [Fintype α] [DecidableEq α]
  [Fintype η] [DecidableEq η] [Fintype κ] [DecidableEq κ]

abbrev InputTerm (α η κ : Type*) := Space α × Matrix κ η ℚ
abbrev OutputTerm (α η κ : Type*) := Space α × Matrix η κ ℚ

def originalShift (z : Space α) : η ⊕ κ → Space α
  | .inl _ => z
  | .inr _ => 0

def scratchShift (z : Space α) : η ⊕ κ → Space α
  | .inl _ => 0
  | .inr _ => z

def gatherPlus (E : Matrix κ η ℚ) : Matrix (η ⊕ κ) (η ⊕ κ) ℚ :=
  Matrix.fromBlocks 1 0 E 1

def consumePlus (D : Matrix η κ ℚ) : Matrix (η ⊕ κ) (η ⊕ κ) ℚ :=
  Matrix.fromBlocks 1 D 0 1

def gatherToken (e : InputTerm α η κ) : Word α (η ⊕ κ) :=
  [.translate (originalShift e.1), .localM (gatherPlus e.2),
    .translate (originalShift e.1)]

def consumeToken (e : OutputTerm α η κ) : Word α (η ⊕ κ) :=
  [.translate (scratchShift e.1), .localM (consumePlus e.2),
    .translate (scratchShift e.1)]

def gatherTerms (es : List (InputTerm α η κ)) : Word α (η ⊕ κ) :=
  es.flatMap gatherToken

def consumeTerms (ds : List (OutputTerm α η κ)) : Word α (η ⊕ κ) :=
  ds.flatMap consumeToken

def inputValue (es : List (InputTerm α η κ)) (f : ℕ)
    (x : Data α (η ⊕ κ) f) (k : κ) (q : Sky α f) : ℂ :=
  (es.map (fun e => ∑ j, (e.2 k j:ℂ)*x (.inl j) (fun i => q i+e.1))).sum

def outputValue (ds : List (OutputTerm α η κ)) (f : ℕ)
    (y : κ → Sky α f → ℂ) (j : η) (q : Sky α f) : ℂ :=
  (ds.map (fun e => ∑ k, (e.2 j k:ℂ)*y k (fun i => q i+e.1))).sum

private theorem cast_indicator (P : Prop) [Decidable P] :
    (((if P then 1 else 0):ℚ):ℂ)=if P then 1 else 0 := by
  split <;> norm_num

private theorem add_twice (q z : Space α) : q+z+z=q := by
  have hz (a : α) : z a+z a=0 := by
    rcases bit_cases (z a) with h|h <;> simp [h] <;> decide
  funext a
  simp only [Pi.add_apply,add_assoc,hz,add_zero]

theorem gatherPlus_original (E : Matrix κ η ℚ) (x : (η ⊕ κ)→ℂ) (j : η) :
    actPoint (gatherPlus E) x (.inl j)=x (.inl j) := by
  simp [actPoint,gatherPlus,Fintype.sum_sum_type,Matrix.one_apply,
    cast_indicator,ite_mul]

theorem gatherPlus_scratch (E : Matrix κ η ℚ) (x : (η ⊕ κ)→ℂ) (k : κ) :
    actPoint (gatherPlus E) x (.inr k)=x (.inr k)+∑ j,(E k j:ℂ)*x (.inl j) := by
  simp [actPoint,gatherPlus,Fintype.sum_sum_type,Matrix.one_apply,
    cast_indicator,ite_mul,add_comm]

theorem consumePlus_original (D : Matrix η κ ℚ) (x : (η ⊕ κ)→ℂ) (j : η) :
    actPoint (consumePlus D) x (.inl j)=x (.inl j)+∑ k,(D j k:ℂ)*x (.inr k) := by
  simp [actPoint,consumePlus,Fintype.sum_sum_type,Matrix.one_apply,
    cast_indicator,ite_mul]

theorem consumePlus_scratch (D : Matrix η κ ℚ) (x : (η ⊕ κ)→ℂ) (k : κ) :
    actPoint (consumePlus D) x (.inr k)=x (.inr k) := by
  simp [actPoint,consumePlus,Fintype.sum_sum_type,Matrix.one_apply,
    cast_indicator,ite_mul]

theorem gatherToken_original (A : (η ⊕ κ)→OBase α) (e : InputTerm α η κ)
    (f : ℕ) (x : Data α (η ⊕ κ) f) (j : η) (q : Sky α f) :
    OriginalGroupedFrameWords.walk A f (gatherToken e) x (.inl j) q=x (.inl j) q := by
  simp [gatherToken,OriginalGroupedFrameWords.walk,OriginalGroupedFrameWords.Move.go,multiAct,point,gatherPlus_original,
    originalShift,act_shift,add_twice]

theorem gatherToken_scratch (A : (η ⊕ κ)→OBase α) (e : InputTerm α η κ)
    (f : ℕ) (x : Data α (η ⊕ κ) f) (k : κ) (q : Sky α f) :
    OriginalGroupedFrameWords.walk A f (gatherToken e) x (.inr k) q=
      x (.inr k) q+∑ j,(e.2 k j:ℂ)*x (.inl j) (fun i => q i+e.1) := by
  simp [gatherToken,OriginalGroupedFrameWords.walk,OriginalGroupedFrameWords.Move.go,multiAct,point,gatherPlus_scratch,
    originalShift,act_shift]

theorem consumeToken_original (A : (η ⊕ κ)→OBase α) (e : OutputTerm α η κ)
    (f : ℕ) (x : Data α (η ⊕ κ) f) (j : η) (q : Sky α f) :
    OriginalGroupedFrameWords.walk A f (consumeToken e) x (.inl j) q=
      x (.inl j) q+∑ k,(e.2 j k:ℂ)*x (.inr k) (fun i => q i+e.1) := by
  simp [consumeToken,OriginalGroupedFrameWords.walk,OriginalGroupedFrameWords.Move.go,multiAct,point,consumePlus_original,
    scratchShift,act_shift]

theorem consumeToken_scratch (A : (η ⊕ κ)→OBase α) (e : OutputTerm α η κ)
    (f : ℕ) (x : Data α (η ⊕ κ) f) (k : κ) (q : Sky α f) :
    OriginalGroupedFrameWords.walk A f (consumeToken e) x (.inr k) q=x (.inr k) q := by
  simp [consumeToken,OriginalGroupedFrameWords.walk,OriginalGroupedFrameWords.Move.go,multiAct,point,consumePlus_scratch,
    scratchShift,act_shift,add_twice]

theorem gatherTerms_original (A : (η ⊕ κ)→OBase α)
    (es : List (InputTerm α η κ)) (f : ℕ) (x : Data α (η ⊕ κ) f)
    (j : η) (q : Sky α f) : OriginalGroupedFrameWords.walk A f (gatherTerms es) x (.inl j) q=x (.inl j) q := by
  induction es generalizing x with
  | nil => rfl
  | cons e es ih =>
    rw [gatherTerms,List.flatMap_cons,OriginalGroupedFrameWords.walk_append]
    exact (ih _).trans (gatherToken_original A e f x j q)

theorem gatherTerms_scratch (A : (η ⊕ κ)→OBase α)
    (es : List (InputTerm α η κ)) (f : ℕ) (x : Data α (η ⊕ κ) f)
    (k : κ) (q : Sky α f) :
    OriginalGroupedFrameWords.walk A f (gatherTerms es) x (.inr k) q=x (.inr k) q+inputValue es f x k q := by
  induction es generalizing x with
  | nil => simp [gatherTerms,OriginalGroupedFrameWords.walk,inputValue]
  | cons e es ih =>
    rw [gatherTerms,List.flatMap_cons,OriginalGroupedFrameWords.walk_append,← gatherTerms,ih]
    simp only [gatherToken_scratch,inputValue,List.map_cons,List.sum_cons]
    simp only [gatherToken_original]
    ring

theorem consumeTerms_scratch (A : (η ⊕ κ)→OBase α)
    (ds : List (OutputTerm α η κ)) (f : ℕ) (x : Data α (η ⊕ κ) f)
    (k : κ) (q : Sky α f) : OriginalGroupedFrameWords.walk A f (consumeTerms ds) x (.inr k) q=x (.inr k) q := by
  induction ds generalizing x with
  | nil => rfl
  | cons d ds ih =>
    rw [consumeTerms,List.flatMap_cons,OriginalGroupedFrameWords.walk_append]
    exact (ih _).trans (consumeToken_scratch A d f x k q)

theorem consumeTerms_original (A : (η ⊕ κ)→OBase α)
    (ds : List (OutputTerm α η κ)) (f : ℕ) (x : Data α (η ⊕ κ) f)
    (j : η) (q : Sky α f) :
    OriginalGroupedFrameWords.walk A f (consumeTerms ds) x (.inl j) q=
      x (.inl j) q+outputValue ds f (fun k => x (.inr k)) j q := by
  induction ds generalizing x with
  | nil => simp [consumeTerms,OriginalGroupedFrameWords.walk,outputValue]
  | cons d ds ih =>
    rw [consumeTerms,List.flatMap_cons,OriginalGroupedFrameWords.walk_append,← consumeTerms,ih]
    simp only [consumeToken_original,outputValue,List.map_cons,List.sum_cons]
    simp only [consumeToken_scratch]
    ring

def polynomialWord (es : List (InputTerm α η κ))
    (ds : List (OutputTerm α η κ)) (S T : Finset α) : Word α (η ⊕ κ) :=
  [.localM (gatherMatrix 0)] ++ gatherTerms es ++
  [.frames (scratchMask S) (scratchMask T)] ++ consumeTerms ds ++
  [.localM (gatherMatrix 0)]

private theorem empty_unframe (A : OBase α) : unframe A ∅=1 := by
  simp [unframe,OBase.proj,wrap_one]

private theorem one_local (A : (η ⊕ κ)→OBase α) (f : ℕ)
    (M : Matrix (η ⊕ κ) (η ⊕ κ) ℚ) (x : Data α (η ⊕ κ) f) :
    OriginalGroupedFrameWords.walk A f [.localM M] x=point f (actPoint M) x := rfl

private theorem one_frame (A : (η ⊕ κ)→OBase α) (f : ℕ)
    (S T : (η ⊕ κ)→Finset α) (x : Data α (η ⊕ κ) f) :
    OriginalGroupedFrameWords.walk A f [.frames S T] x=
      multiAct f (fun l => frame (A l) (T l)*unframe (A l) (S l)) x := rfl

/-- A single physical request per scratch row, after ALL translated inputs
are gathered. The specification includes every original consumer. -/
theorem polynomialWord_correct (A : (η ⊕ κ)→OBase α)
    (es : List (InputTerm α η κ)) (ds : List (OutputTerm α η κ))
    (S T : Finset α) (f : ℕ) (x : Data α (η ⊕ κ) f) (j : η) (q : Sky α f) :
    OriginalGroupedFrameWords.walk A f (polynomialWord es ds S T) x (.inl j) q=
      x (.inl j) q+outputValue ds f
        (fun k => matAct f (frame (A (.inr k)) T*unframe (A (.inr k)) S)
          (inputValue es f x k)) j q := by
  let cleared := point f (actPoint (gatherMatrix (0 : Matrix κ η ℚ))) x
  have hs (k : κ) :
      OriginalGroupedFrameWords.walk A f (gatherTerms es) cleared (.inr k)=
        inputValue es f x k := by
    funext w
    rw [gatherTerms_scratch]
    simp [cleared,point,gather_scratch,inputValue,gather_original]
  dsimp only [cleared] at hs
  simp only [polynomialWord,OriginalGroupedFrameWords.walk_append,one_local,one_frame,
    point,gather_original]
  rw [consumeTerms_original]
  simp only [multiAct,scratchMask,empty_unframe,frame_zero,Matrix.mul_one,
    matAct_one,gatherTerms_original]
  simp only [hs]
  simp only [point,gather_original]

theorem polynomialWord_scratch_zero (A : (η ⊕ κ)→OBase α)
    (es : List (InputTerm α η κ)) (ds : List (OutputTerm α η κ))
    (S T : Finset α) (f : ℕ) (x : Data α (η ⊕ κ) f) (k : κ) :
    OriginalGroupedFrameWords.walk A f (polynomialWord es ds S T) x (.inr k)=0 := by
  funext q
  simp [polynomialWord,OriginalGroupedFrameWords.walk_append,OriginalGroupedFrameWords.walk,OriginalGroupedFrameWords.Move.go,point,gather_scratch]

private theorem gatherTerms_charge (X : Layout α) (r f : ℕ) (tau : ℕ→ℕ)
    (es : List (InputTerm α η κ)) : wordCharge X r f tau (gatherTerms es)=0 := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simpa [gatherTerms,List.flatMap_cons,gatherToken,wordCharge,
      List.map_append,List.sum_append,moveCharge] using ih

private theorem consumeTerms_charge (X : Layout α) (r f : ℕ) (tau : ℕ→ℕ)
    (ds : List (OutputTerm α η κ)) : wordCharge X r f tau (consumeTerms ds)=0 := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simpa [consumeTerms,List.flatMap_cons,consumeToken,wordCharge,
      List.map_append,List.sum_append,moveCharge] using ih

/-- All translations and fixed coefficient maps have paid local work but
zero child bills. Spectator repetitions in the ONE common batch remain. -/
theorem polynomialWord_charge (X : Layout α) (r f : ℕ) (tau : ℕ→ℕ)
    (es : List (InputTerm α η κ)) (ds : List (OutputTerm α η κ)) (S T : Finset α) :
    wordCharge X r f tau (polynomialWord es ds S T)=
      Fintype.card κ * (if ((S\T) ∪ (T\S)).card=0 then 0 else
        (2^r*(2^f)^(X.n-((S\T) ∪ (T\S)).card))*tau (((S\T) ∪ (T\S)).card*f)) := by
  have he := gatherTerms_charge X r f tau es
  have hd := consumeTerms_charge X r f tau ds
  simp only [wordCharge] at he hd
  simp [polynomialWord,wordCharge,List.map_append,List.sum_append,moveCharge,
    he,hd,frameCharge,residualRank,scratchMask,Fintype.sum_sum_type]

section RAM
universe U
variable {ι : Type U} {m : Bool} {cl : Paint} {f : ι→ℕ}
  {s : Ty} {x : ι→T s} {X : Layout α} {R0 : Layout η} {r : ℕ}
  {v : ∀ i, Grain α η r (f i)}

/-- Starts with original input only. Every scratch zero, coefficient,
route, point operation, memory access and control step has native code. -/
theorem polynomialWord_native (b : Bank (hatch cl) ι)
    (h : Rig m b.B f s x cl X R0 r v) (R : Layout (η ⊕ κ)) (j : η)
    (hr : 3≤X.n) (A : (η ⊕ κ)→OBase α) (tau : ι→ℕ→ℕ)
    (HC : ∀ n : ℕ, 0<n → n≤X.n → GroupedResidual.Rig.RawContract cl b
      (fun i => n*f i) (fun i => tau i (n*f i)))
    (es : List (InputTerm α η κ)) (ds : List (OutputTerm α η κ)) (S T : Finset α) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape
        (coastline A r (f i) (polynomialWord es ds S T) (padded (v i))))
      (fun i => (fleet X R0 r (f i)).n)
      (fun i => Fintype.card κ * (if ((S\T) ∪ (T\S)).card=0 then 0 else
        (2^r*(2^f i)^(X.n-((S\T) ∪ (T\S)).card))*tau i (((S\T) ∪ (T\S)).card*f i))) := by
  let env i : Ty.T (p s (bundle cl)) :=
    (x i,(fleet X R r (f i)).tape (padded (κ:=κ) (v i)))
  have hg := h.gather id env (t:=p s (bundle cl)) Can.first
  have hp : Rig m b.B f (p s (bundle cl)) env cl X R r
      (fun i => padded (κ:=κ) (v i)) := ⟨hg.gear,hg.imag,Can.second⟩
  have HF := OriginalGroupedFrameCompilerRAM.frame_service cl m X R r hr f A b tau HC
  have HS := OriginalGroupedWordRAM.sweep A b tau HF hp (polynomialWord es ds S T)
  have H := (Able.of_can (b:=b) (prepare_scratch h R)).save_keep HS
  simp only [polynomialWord_charge,Nat.zero_add] at H
  apply H.weaken ?_ (fun _ => Nat.le_refl _)
  refine ⟨R.n+1,fun i => ?_⟩
  have hw := workspace_width (X:=X) (R0:=R0) (r:=r) R j (f i)
  dsimp
  nlinarith
end RAM

end
end FourierSchur.OriginalTranslatedBankPolynomialRAM
