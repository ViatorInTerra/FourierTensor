import work_in_progress.OriginalContextualChirpWords
import work_in_progress.OriginalPhysicalQuarterPhaseRAM

/-! A paid word language for general quadratic adapters. Fourth-root
physical phases include the full i^f amplification factor. Each adapter
contains exactly one existing frame-ratio batch, with its full additive
spectator bill. Every other step is actual local RAM code. -/
namespace FourierSchur.OriginalQuadraticAdapterWords
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty Matrix Finset
open OriginalPhysicalQuarterPhaseRAM
noncomputable section

inductive Step (α ρ : Type*)
  | old (g : OriginalContextualChirpWords.Step α ρ)
  | quarter (l : ρ) (rows : List (Option α))

abbrev Word (α ρ : Type*) := List (Step α ρ)

section Semantics
variable {α ρ : Type*} [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ]

def Step.go (A : ρ→OBase α) (f : ℕ) : Step α ρ→Data α ρ f→Data α ρ f
  | .old g => g.go A f
  | .quarter l rows => fun x role q => if role=l then
      quarterFactor (fun j : Fin rows.length => rows.get j) f q*x role q else x role q

def walk (A : ρ→OBase α) (f : ℕ) (p : Word α ρ) (x : Data α ρ f) :=
  p.foldl (fun x g => g.go A f x) x

def ferry (A : ρ→OBase α) (r f : ℕ) (g : Step α ρ)
    (v : Grain α ρ r f) : Grain α ρ r f :=
  fun q => g.go A f (fun role z => v (role,q.2.1,z)) q.1 q.2.2

def coastline (A : ρ→OBase α) (r f : ℕ) (p : Word α ρ)
    (v : Grain α ρ r f) : Grain α ρ r f :=
  fun q => walk A f p (fun role z => v (role,q.2.1,z)) q.1 q.2.2

theorem coast_cons (A : ρ→OBase α) (r f : ℕ) (g : Step α ρ)
    (p : Word α ρ) (v : Grain α ρ r f) :
    coastline A r f (g::p) v=coastline A r f p (ferry A r f g v) := rfl

theorem embed_walk (A : ρ→OBase α) (f : ℕ)
    (p : OriginalContextualChirpWords.Word α ρ) (x : Data α ρ f) :
    walk A f (p.map Step.old) x=OriginalContextualChirpWords.walk A f p x := by
  induction p generalizing x with
  | nil => rfl
  | cons g tail ih => exact ih (g.go A f x)

def stepCharge (X : Layout α) (r f : ℕ) (tau : ℕ→ℕ) : Step α ρ→ℕ
  | .old g => OriginalContextualChirpWords.stepCharge X r f tau g
  | .quarter _ _ => 0

def wordCharge (X : Layout α) (r f : ℕ) (tau : ℕ→ℕ) (p : Word α ρ) :=
  (p.map (stepCharge X r f tau)).sum

def soloSubset (l : ρ) (T : Finset α) (role : ρ) : Finset α :=
  if role=l then T else ∅

/-- The phase factors have already been contracted before emission.
`none` entries in leftRows retain the nontrivial global i^(gamma*f). -/
def adapterWord (l : ρ) (T : Finset α)
    (Mright Mleft : Matrix α α F) (zright : Space α)
    (rightRows leftRows : List (Option α)) (edges : List (α×α)) : Word α ρ :=
  [.old (.affine l Mright zright), .quarter l rightRows,
   .old (.chirp l edges), .old (.native (.frames (fun _ => ∅) (soloSubset l T))),
   .quarter l leftRows, .old (.chirp l edges), .old (.affine l Mleft 0)]

/-- Every original auxiliary bank remains arbitrary and is returned
unchanged when this selected-role adapter is inserted in a larger word. -/
theorem adapter_off (A : ρ→OBase α) (f : ℕ) (x : Data α ρ f)
    (l role : ρ) (he : role≠l) (T : Finset α)
    (Mright Mleft : Matrix α α F) (zright : Space α)
    (rightRows leftRows : List (Option α)) (edges : List (α×α)) :
    walk A f (adapterWord l T Mright Mleft zright rightRows leftRows edges) x role=x role := by
  funext q
  simp [adapterWord,walk,Step.go,OriginalContextualChirpWords.Step.go,
    OriginalGroupedFrameWords.Move.go,soloSubset,he,multiAct,
    unframe,OBase.proj,wrap_one,matAct_one]

/-- One selected kernel batch; none of the phase/routing steps duplicates
its recursive coefficient. Their zero child bill does not mean free work. -/
theorem adapter_charge (X : Layout α) (r f : ℕ) (tau : ℕ→ℕ)
    (l : ρ) (T : Finset α) (Mright Mleft : Matrix α α F) (zright : Space α)
    (rightRows leftRows : List (Option α)) (edges : List (α×α)) :
    wordCharge X r f tau (adapterWord l T Mright Mleft zright rightRows leftRows edges)=
      if T.card=0 then 0 else 2^r*(2^f)^(X.n-T.card)*tau (T.card*f) := by
  simp only [wordCharge,adapterWord,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    stepCharge,OriginalContextualChirpWords.stepCharge,
    OriginalGroupedWordRAM.moveCharge,zero_add,add_zero]
  unfold OriginalGroupedWordRAM.frameCharge OriginalGroupedWordRAM.residualRank
  rw [Finset.sum_eq_single l]
  · simp [soloSubset]
  · intro role _ he
    simp [soloSubset,he]
  · simp

/-- Nonalternating polar forms admit an I_r congruence. Their complete
adapter contains no physical chirp or fourth-root phase step. -/
def affineAdapterWord (l : ρ) (T : Finset α)
    (Mright Mleft : Matrix α α F) (zright : Space α) : Word α ρ :=
  [.old (.affine l Mright zright),
   .old (.native (.frames (fun _ => ∅) (soloSubset l T))),
   .old (.affine l Mleft 0)]

theorem affine_adapter_charge (X : Layout α) (r f : ℕ) (tau : ℕ→ℕ)
    (l : ρ) (T : Finset α) (Mright Mleft : Matrix α α F) (zright : Space α) :
    wordCharge X r f tau (affineAdapterWord l T Mright Mleft zright)=
      if T.card=0 then 0 else 2^r*(2^f)^(X.n-T.card)*tau (T.card*f) := by
  simpa [wordCharge,affineAdapterWord,adapterWord,stepCharge,
    OriginalContextualChirpWords.stepCharge,OriginalGroupedWordRAM.moveCharge] using
    adapter_charge X r f tau l T Mright Mleft zright [] [] []

theorem affine_adapter_off (A : ρ→OBase α) (f : ℕ) (x : Data α ρ f)
    (l role : ρ) (he : role≠l) (T : Finset α)
    (Mright Mleft : Matrix α α F) (zright : Space α) :
    walk A f (affineAdapterWord l T Mright Mleft zright) x role=x role := by
  funext q
  simp [affineAdapterWord,walk,Step.go,OriginalContextualChirpWords.Step.go,
    OriginalGroupedFrameWords.Move.go,soloSubset,he,multiAct,
    unframe,OBase.proj,wrap_one,matAct_one]
end Semantics

section Compiler
universe U
variable {α ρ : Type*} [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ] {ι : Type U}
  {m : Bool} {cl : Paint} {f : ι→ℕ} {s : Ty} {x : ι→T s}
  {X : Layout α} {R : Layout ρ} {r : ℕ}
  {v : ∀ i, Grain α ρ r (f i)}

theorem open_step (A : ρ→OBase α) (b : Bank (hatch cl) ι) (tau : ι→ℕ→ℕ)
    (Hframes : OriginalGroupedWordRAM.FrameService
      (m:=m) (f:=f) (X:=X) (R:=R) (r:=r) A b tau)
    (h : Rig m b.B f s x cl X R r v) (hr : 3≤X.n) (g : Step α ρ) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (ferry A r (f i) g (v i)))
      (fun i => (fleet X R r (f i)).n)
      (fun i => stepCharge X r (f i) (tau i) g) := by
  cases g with
  | old g =>
    simpa only [stepCharge,ferry,Step.go,OriginalContextualChirpWords.ferry] using
      OriginalContextualChirpWords.open_step A b tau Hframes h hr g
  | quarter l rows =>
    have H := Able.of_can (b:=b) (quarterData_native h (by omega) l
      (fun j : Fin rows.length => rows.get j))
    simpa only [stepCharge,ferry,Step.go,quarterData] using H

/-- Actual open native program, charging all local operations and retaining
the exact additive coefficient of every existing recursive frame request. -/
theorem sweep (A : ρ→OBase α) (b : Bank (hatch cl) ι) (tau : ι→ℕ→ℕ)
    (Hframes : OriginalGroupedWordRAM.FrameService
      (m:=m) (f:=f) (X:=X) (R:=R) (r:=r) A b tau)
    (h : Rig m b.B f s x cl X R r v) (hr : 3≤X.n) (p : Word α ρ) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (coastline A r (f i) p (v i)))
      (fun i => (fleet X R r (f i)).n)
      (fun i => wordCharge X r (f i) (tau i) p) := by
  induction p generalizing s v with
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
    have K := (open_step A b tau Hframes h hr g).save_keep H
    simpa only [wordCharge,List.map_cons,List.sum_cons,coast_cons] using K

theorem native_sweep (A : ρ→OBase α) (b : Bank (hatch cl) ι) (tau : ι→ℕ→ℕ)
    (h : Rig m b.B f s x cl X R r v) (hr : 3≤X.n)
    (HC : ∀ n : ℕ, 0<n → n≤X.n → GroupedResidual.Rig.RawContract cl b
      (fun i => n*f i) (fun i => tau i (n*f i))) (p : Word α ρ) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (coastline A r (f i) p (v i)))
      (fun i => (fleet X R r (f i)).n)
      (fun i => wordCharge X r (f i) (tau i) p) :=
  sweep A b tau (OriginalGroupedFrameCompilerRAM.frame_service cl m X R r hr f A b tau HC)
    h hr p
end Compiler
end
end FourierSchur.OriginalQuadraticAdapterWords
