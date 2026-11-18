import work_in_progress.OriginalTranslatedBankPolynomialRAM

/-! Native compilation of a complete bank DAG with explicitly allocated
scratch. Each source gather is an actual rational point pass, followed by
one selected native frame request and its paid address translation. The
final point pass writes all original outputs and clears every scratch role.
-/
namespace FourierSchur.OriginalNativeBankDAG
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty Matrix Finset
open OriginalGroupedFrameWords OriginalGroupedWordRAM
open OriginalLocalizedBankWorkspaceRAM
noncomputable section

variable {α η κ : Type*} [Fintype α] [DecidableEq α]
  [Fintype η] [DecidableEq η] [Fintype κ] [DecidableEq κ]

structure Node (α η κ : Type*) where
  slot : κ
  coeff : (η⊕κ)→ℚ
  sourceMask : Finset α
  targetMask : Finset α
  offset : Space α

def overwrite (k : κ) (coeff : (η⊕κ)→ℚ) : Matrix (η⊕κ) (η⊕κ) ℚ :=
  fun i j => if i=Sum.inr k then coeff j else if i=j then 1 else 0

def oneMask (k : κ) (S : Finset α) : (η⊕κ)→Finset α :=
  fun i => if i=Sum.inr k then S else ∅

def oneShift (k : κ) (z : Space α) : (η⊕κ)→Space α :=
  fun i => if i=Sum.inr k then z else 0

def nodeWord (g : Node α η κ) : Word α (η⊕κ) :=
  [.localM (overwrite g.slot g.coeff),
   .frames (oneMask g.slot g.sourceMask) (oneMask g.slot g.targetMask),
   .translate (oneShift g.slot g.offset)]

def nodeValue (A : (η⊕κ)→OBase α) (f : ℕ) (g : Node α η κ)
    (x : Data α (η⊕κ) f) : Data α (η⊕κ) f :=
  fun role => if role=Sum.inr g.slot then
    matAct f (shift g.offset*(frame (A (.inr g.slot)) g.targetMask*
      unframe (A (.inr g.slot)) g.sourceMask))
      (fun q => ∑ j,(g.coeff j:ℂ)*x j q)
    else x role

private theorem cast_indicator (P : Prop) [Decidable P] :
    (((if P then 1 else 0):ℚ):ℂ)=if P then 1 else 0 := by
  split <;> norm_num

theorem overwrite_slot (k : κ) (coeff : (η⊕κ)→ℚ) (x : (η⊕κ)→ℂ) :
    actPoint (overwrite k coeff) x (.inr k)=∑ j,(coeff j:ℂ)*x j := by
  simp [actPoint,overwrite]

theorem overwrite_off (k : κ) (coeff : (η⊕κ)→ℚ) (x : (η⊕κ)→ℂ)
    (i : η⊕κ) (hi : i≠Sum.inr k) : actPoint (overwrite k coeff) x i=x i := by
  simp [actPoint,overwrite,hi,cast_indicator]

theorem nodeWord_correct (A : (η⊕κ)→OBase α) (f : ℕ)
    (g : Node α η κ) (x : Data α (η⊕κ) f) :
    walk A f (nodeWord g) x=nodeValue A f g x := by
  funext role q
  by_cases h : role=Sum.inr g.slot
  · subst role
    simp [nodeWord,OriginalGroupedFrameWords.walk,OriginalGroupedFrameWords.Move.go,nodeValue,oneMask,oneShift,multiAct,
      OAI.PowerSaving.Binary.point,overwrite_slot,matAct_mul,Matrix.mul_assoc]
    have hg : OAI.PowerSaving.Binary.point f (actPoint (overwrite g.slot g.coeff)) x (.inr g.slot)=
        (fun w => ∑ j,(g.coeff j:ℂ)*x j w) := by
      funext w
      exact overwrite_slot _ _ _
    rw [hg]
    simp only [Fintype.sum_sum_type]
  · simp [nodeWord,OriginalGroupedFrameWords.walk,OriginalGroupedFrameWords.Move.go,nodeValue,oneMask,oneShift,multiAct,
      OAI.PowerSaving.Binary.point,h,overwrite_off,unframe,OBase.proj,wrap_one,shift_zero]

def finish (D : Matrix η (η⊕κ) ℚ) : Matrix (η⊕κ) (η⊕κ) ℚ
  | .inl i,j => D i j
  | .inr _,_ => 0

def programWord (p : List (Node α η κ)) (D : Matrix η (η⊕κ) ℚ) : Word α (η⊕κ) :=
  p.flatMap nodeWord++[.localM (finish D)]

def evaluate (A : (η⊕κ)→OBase α) (f : ℕ) (p : List (Node α η κ))
    (D : Matrix η (η⊕κ) ℚ) (x : Data α (η⊕κ) f) : Data α (η⊕κ) f :=
  point f (actPoint (finish D)) (p.foldl (fun y g => nodeValue A f g y) x)

theorem nodeWords_correct (A : (η⊕κ)→OBase α) (f : ℕ)
    (p : List (Node α η κ)) (x : Data α (η⊕κ) f) :
    walk A f (p.flatMap nodeWord) x=p.foldl (fun y g => nodeValue A f g y) x := by
  induction p generalizing x with
  | nil => rfl
  | cons g p ih =>
    rw [List.flatMap_cons,OriginalGroupedFrameWords.walk_append,nodeWord_correct,ih]
    rfl

theorem programWord_correct (A : (η⊕κ)→OBase α) (f : ℕ)
    (p : List (Node α η κ)) (D : Matrix η (η⊕κ) ℚ) (x : Data α (η⊕κ) f) :
    walk A f (programWord p D) x=evaluate A f p D x := by
  rw [programWord,OriginalGroupedFrameWords.walk_append,nodeWords_correct]
  rfl

theorem evaluate_original (A : (η⊕κ)→OBase α) (f : ℕ)
    (p : List (Node α η κ)) (D : Matrix η (η⊕κ) ℚ) (x : Data α (η⊕κ) f)
    (i : η) (q : Sky α f) :
    evaluate A f p D x (.inl i) q=
      ∑ j,(D i j:ℂ)*(p.foldl (fun y g => nodeValue A f g y) x) j q := by
  simp [evaluate,point,actPoint,finish]

theorem evaluate_scratch (A : (η⊕κ)→OBase α) (f : ℕ)
    (p : List (Node α η κ)) (D : Matrix η (η⊕κ) ℚ) (x : Data α (η⊕κ) f)
    (k : κ) : evaluate A f p D x (.inr k)=0 := by
  funext q
  simp [evaluate,point,actPoint,finish]

def nodeRank (g : Node α η κ) : ℕ :=
  ((g.sourceMask\g.targetMask)∪(g.targetMask\g.sourceMask)).card

def nodeCharge (X : Layout α) (r f : ℕ) (tau : ℕ→ℕ) (g : Node α η κ) : ℕ :=
  if nodeRank g=0 then 0 else 2^r*(2^f)^(X.n-nodeRank g)*tau (nodeRank g*f)

theorem nodeWord_charge (X : Layout α) (r f : ℕ) (tau : ℕ→ℕ)
    (g : Node α η κ) : wordCharge X r f tau (nodeWord g)=nodeCharge X r f tau g := by
  have hrank (role : η⊕κ) :
      residualRank (oneMask g.slot g.sourceMask) (oneMask g.slot g.targetMask) role=
        if role=Sum.inr g.slot then nodeRank g else 0 := by
    by_cases h : role=Sum.inr g.slot <;> simp [residualRank,oneMask,nodeRank,h]
  simp only [wordCharge,nodeWord,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    moveCharge,zero_add,add_zero]
  unfold frameCharge
  rw [Finset.sum_eq_single (Sum.inr g.slot)]
  · rw [hrank]
    simp [nodeCharge]
  · intro role _ hrole
    rw [hrank]
    simp [hrole]
  · simp

theorem programWord_charge (X : Layout α) (r f : ℕ) (tau : ℕ→ℕ)
    (p : List (Node α η κ)) (D : Matrix η (η⊕κ) ℚ) :
    wordCharge X r f tau (programWord p D)=(p.map (nodeCharge X r f tau)).sum := by
  have hadd (a b : Word α (η⊕κ)) : wordCharge X r f tau (a++b)=
      wordCharge X r f tau a+wordCharge X r f tau b := by
    simp [wordCharge,List.map_append,List.sum_append]
  induction p with
  | nil => simp [programWord,wordCharge,moveCharge]
  | cons g p ih =>
    change wordCharge X r f tau (nodeWord g++programWord p D)=_
    rw [hadd,nodeWord_charge,ih]
    rfl

section Native
universe U
variable {ι : Type U} {m : Bool} {cl : Paint} {f : ι→ℕ}
  {s : Ty} {x : ι→T s} {X : Layout α} {R0 : Layout η} {r : ℕ}
  {v : ∀ i,Grain α η r (f i)}

/-- An actual open RAM program for the complete list, starting from only
the original input banks. Fresh scratch allocation and every point, route,
coefficient table and control pass are paid. The additive child price is
unchanged when the local allowance is reduced to original input width. -/
theorem fresh_native (b : Bank (hatch cl) ι)
    (h : Rig m b.B f s x cl X R0 r v) (R : Layout (η⊕κ)) (j : η)
    (hr : 3≤X.n) (A : (η⊕κ)→OBase α) (tau : ι→ℕ→ℕ)
    (HC : ∀ n : ℕ,0<n → n≤X.n → GroupedResidual.Rig.RawContract cl b
      (fun i => n*f i) (fun i => tau i (n*f i)))
    (p : List (Node α η κ)) (D : Matrix η (η⊕κ) ℚ) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape
        (coastline A r (f i) (programWord p D) (padded (v i))))
      (fun i => (fleet X R0 r (f i)).n)
      (fun i => (p.map (nodeCharge X r (f i) (tau i))).sum) := by
  let env i : T (Ty.p s (bundle cl)) :=
    (x i,(fleet X R r (f i)).tape (padded (κ:=κ) (v i)))
  have hg := h.gather id env (t:=Ty.p s (bundle cl)) Can.first
  have hp : Rig m b.B f (Ty.p s (bundle cl)) env cl X R r
      (fun i => padded (κ:=κ) (v i)) := ⟨hg.gear,hg.imag,Can.second⟩
  have HF := OriginalGroupedFrameCompilerRAM.frame_service cl m X R r hr f A b tau HC
  have HS := OriginalGroupedWordRAM.sweep A b tau HF hp (programWord p D)
  have H := (Able.of_can (b:=b) (prepare_scratch h R)).save_keep HS
  have H' : Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape
        (coastline A r (f i) (programWord p D) (padded (v i))))
      (fun i => (fleet X R r (f i)).n)
      (fun i => (p.map (nodeCharge X r (f i) (tau i))).sum) := by
    simpa only [Nat.zero_add,programWord_charge] using H
  apply H'.weaken ?_ (fun _ => Nat.le_refl _)
  refine ⟨R.n+1,fun i => ?_⟩
  have hw := workspace_width (X:=X) (R0:=R0) (r:=r) R j (f i)
  dsimp
  nlinarith

end Native

end
end FourierSchur.OriginalNativeBankDAG
