import work_in_progress.OriginalGroupedFrameWords
import work_in_progress.OriginalGroupedRecursionRAM

/-!
Paid compiler architecture for retained grouped frame words.

Point tokens and all-role translations are implemented by the existing
actual scalar/address RAM loops. `sweep` composes their real closed code
with the paid open whole-residual frame service, retaining additive child
charges. No dense frame application or selected-bit conversion is treated
as a primitive. The concrete frame service is supplied by the whole-
residual adapter, after the frame-ratio factorization is proved.
-/

namespace FourierSchur.OriginalGroupedWordRAM

open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty Matrix Finset
open scoped BigOperators
noncomputable section

namespace G
abbrev Move := OriginalGroupedFrameWords.Move
abbrev Word := OriginalGroupedFrameWords.Word
end G

section Semantics
variable {α ρ : Type*} [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ]

def ferry (A : ρ → OBase α) (r f : Nat) (g : G.Move α ρ)
    (v : Grain α ρ r f) : Grain α ρ r f :=
  fun x => g.go A f (fun l j => v (l,x.2.1,j)) x.1 x.2.2

def coastline (A : ρ → OBase α) (r f : Nat) (p : G.Word α ρ)
    (v : Grain α ρ r f) : Grain α ρ r f :=
  fun x => OriginalGroupedFrameWords.walk A f p
    (fun l j => v (l,x.2.1,j)) x.1 x.2.2

theorem coast_cons (A : ρ → OBase α) (r f : Nat) (g : G.Move α ρ)
    (p : G.Word α ρ) (v : Grain α ρ r f) :
    coastline A r f (g::p) v = coastline A r f p (ferry A r f g v) := rfl

def residualRank (s t : ρ → Finset α) (l : ρ) : Nat :=
  ((s l \ t l) ∪ (t l \ s l)).card

def frameCharge (X : Layout α) (r f : Nat) (s t : ρ → Finset α)
    (tau : Nat → Nat) : Nat :=
  ∑ l, if residualRank s t l = 0 then 0 else
    (2^r * (2^f)^(X.n-residualRank s t l)) * (tau (residualRank s t l*f))

def moveCharge (X : Layout α) (r f : Nat) (tau : Nat → Nat) : G.Move α ρ → Nat
  | .localM _ => 0
  | .frames s t => frameCharge X r f s t tau
  | .translate _ => 0

def wordCharge (X : Layout α) (r f : Nat) (tau : Nat → Nat)
    (p : G.Word α ρ) : Nat := (p.map (moveCharge X r f tau)).sum

theorem wordCharge_nil (X : Layout α) (r f : Nat) (tau : Nat → Nat) :
    wordCharge X r f tau ([] : G.Word α ρ) = 0 := rfl

theorem wordCharge_cons (X : Layout α) (r f : Nat) (tau : Nat → Nat)
    (g : G.Move α ρ) (p : G.Word α ρ) :
    wordCharge X r f tau (g::p) = moveCharge X r f tau g + wordCharge X r f tau p :=
  rfl

end Semantics

section Compiler
universe U
variable {α ρ : Type*} [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ] {ι : Type U}
variable {m : Bool} {B f : ι → Nat} {s : Ty} {x : ι → T s}
  {cl : Paint} {X : Layout α} {R : Layout ρ} {r : Nat}
  {v : ∀ i, Grain α ρ r (f i)}

/-- Actual prepared rational coefficient loops; all role inputs remain live. -/
theorem point_cost (A : ρ → OBase α) (h : Rig m B f s x cl X R r v)
    (M : Matrix ρ ρ ℚ) :
    Can m B s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (ferry A r (f i) (.localM M) (v i)))
      (fun i => (fleet X R r (f i)).n) := by
  simpa [ferry,OriginalGroupedFrameWords.Move.go,OAI.PowerSaving.RAM.ferry,
    OAI.PowerSaving.Binary.Move.go] using h.point_cost M

/-- One finite-role dispatch per output. The underlying shift reads use the
already-paid prefix/address tables; no column scan or free permutation. -/
theorem translate_read (A : ρ → OBase α) (h : Rig m B f s x cl X R r v)
    (z : ρ → Space α) (q : ∀ i, Beach α ρ r (f i))
    (g : Knows m B s x fun i => (fleet X R r (f i)).loc (q i)) :
    Has m B s (c cl) x fun i => ferry A r (f i) (.translate z) (v i) (q i) := by
  obtain ⟨hl,hk⟩ := h.addrs q g
  apply Can.cases_code (q:=fun i => (q i).1) R hl
  intro l
  have H := (h.ferry_shift l (z l) q g).reindex
    (fun i : {i // (q i).1=l} => i.1)
  apply H.cong (fun _ => rfl)
  intro i
  simp [ferry,OriginalGroupedFrameWords.Move.go,multiAct,
    OAI.PowerSaving.RAM.ferry,OAI.PowerSaving.Binary.Move.go,roleAct,i.2]

theorem translate_cost (A : ρ → OBase α) (h : Rig m B f s x cl X R r v)
    (z : ρ → Space α) :
    Can m B s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (ferry A r (f i) (.translate z) (v i)))
      (fun i => (fleet X R r (f i)).n) := by
  refine h.chart _ ?_
  let S := Σ i, Beach α ρ r (f i)
  have hg := h.gather (fun d : S => d.1)
    (fun d => ((x d.1,(fleet X R r (f d.1)).loc d.2) : T (p s w)))
    (t:=p s w) Can.first
  exact translate_read A hg z (fun d => d.2) Can.second

variable (A : ρ → OBase α) (b : Bank (hatch cl) ι) (tau : ι → Nat → Nat)

/-- The service must be a paid open RAM program for the entire frame block.
It is not an operator oracle or a profile-only complexity hypothesis. -/
def FrameService : Prop :=
  ∀ (s : Ty) (x : ι → T s) (v : ∀ i, Grain α ρ r (f i))
    (h : Rig m b.B f s x cl X R r v) (S T : ρ → Finset α),
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (ferry A r (f i) (.frames S T) (v i)))
      (fun i => (fleet X R r (f i)).n)
      (fun i => frameCharge X r (f i) S T (tau i))

theorem open_move (Hframes : FrameService (m:=m) (f:=f) (X:=X) (R:=R) (r:=r) A b tau)
    (h : Rig m b.B f s x cl X R r v) (g : G.Move α ρ) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (ferry A r (f i) g (v i)))
      (fun i => (fleet X R r (f i)).n)
      (fun i => moveCharge X r (f i) (tau i) g) := by
  cases g with
  | localM M => exact Able.of_can (point_cost A h M)
  | translate z => exact Able.of_can (translate_cost A h z)
  | frames S T => exact Hframes s x v h S T

/-- An actual open-code sweep, preserving old environment/address tables
while replacing the full live role array after every token. Recursive
charges are added verbatim, not multiplied by the local constants. -/
theorem sweep (Hframes : FrameService (m:=m) (f:=f) (X:=X) (R:=R) (r:=r) A b tau)
    (h : Rig m b.B f s x cl X R r v) (P : G.Word α ρ) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (coastline A r (f i) P (v i)))
      (fun i => (fleet X R r (f i)).n)
      (fun i => wordCharge X r (f i) (tau i) P) := by
  induction P generalizing s v with
  | nil =>
    exact (Able.of_can (b:=b) (h.items.mono
      (W':=fun i => (fleet X R r (f i)).n) (fun _ => Nat.zero_le _))).cong
        (fun _ => rfl) (fun _ => rfl)
  | cons g tail ih =>
    let v' i := ferry A r (f i) g (v i)
    let env i : T (p s (bundle cl)) := (x i,(fleet X R r (f i)).tape (v' i))
    have hg := h.gather id env (t:=p s (bundle cl)) Can.first
    have next : Rig m b.B f (p s (bundle cl)) env cl X R r v' :=
      ⟨hg.gear,hg.imag,Can.second⟩
    have H := ih next
    have K := (open_move A b tau Hframes h g).save_keep H
    simpa only [wordCharge_cons,coast_cons] using K

end Compiler
end
end FourierSchur.OriginalGroupedWordRAM
