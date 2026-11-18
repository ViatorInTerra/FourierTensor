import work_in_progress.OriginalPhysicalChirpRAM
import work_in_progress.OriginalPhysicalAffineRAM
import work_in_progress.OriginalGroupedFrameCompilerRAM

/-!
Extend the actual shared word with paid physical-coordinate chirps. Existing
non-butterfly words embed without changing semantics or child bills. The new
primitive is not a commuting Fourier multiplier. Its preparation and data
work are compiled by PhysicalChirpRAM, not assumed as an execution oracle.
-/
namespace FourierSchur.OriginalContextualChirpWords
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty Matrix Finset
open OriginalPhysicalChirpRAM
noncomputable section

inductive Step (α ρ : Type*)
  | native (g : OriginalGroupedFrameWords.Move α ρ)
  | chirp (l : ρ) (edges : List (α × α))
  | affine (l : ρ) (M : Matrix α α OAI.PowerSaving.Binary.F)
      (z : OAI.PowerSaving.Binary.Space α)

abbrev Word (α ρ : Type*) := List (Step α ρ)

section Semantics
variable {α ρ : Type*} [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ]

def Step.go (A : ρ → OBase α) (f : ℕ) : Step α ρ → Data α ρ f → Data α ρ f
  | .native g => g.go A f
  | .chirp l edges => fun x role q =>
      if role=l then chirpFactor (fun j : Fin edges.length => edges.get j) f q*x role q
      else x role q
  | .affine l M z => fun x role q =>
      if role=l then x role (fun j => OriginalPhysicalAffineRAM.affine M z (q j))
      else x role q

def walk (A : ρ → OBase α) (f : ℕ) (p : Word α ρ) (x : Data α ρ f) :=
  p.foldl (fun x g => g.go A f x) x

def ferry (A : ρ → OBase α) (r f : ℕ) (g : Step α ρ)
    (v : Grain α ρ r f) : Grain α ρ r f :=
  fun q => g.go A f (fun role z => v (role,q.2.1,z)) q.1 q.2.2

def coastline (A : ρ → OBase α) (r f : ℕ) (p : Word α ρ)
    (v : Grain α ρ r f) : Grain α ρ r f :=
  fun q => walk A f p (fun role z => v (role,q.2.1,z)) q.1 q.2.2

theorem coast_cons (A : ρ → OBase α) (r f : ℕ) (g : Step α ρ)
    (p : Word α ρ) (v : Grain α ρ r f) :
    coastline A r f (g::p) v=coastline A r f p (ferry A r f g v) := rfl

/-- All original shared-network words remain available verbatim. -/
theorem embed_walk (A : ρ → OBase α) (f : ℕ)
    (p : OriginalGroupedFrameWords.Word α ρ) (x : Data α ρ f) :
    walk A f (p.map Step.native) x=OriginalGroupedFrameWords.walk A f p x := by
  induction p generalizing x with
  | nil => rfl
  | cons g p ih => exact ih (g.go A f x)

def stepCharge (X : Layout α) (r f : ℕ) (tau : ℕ→ℕ) : Step α ρ → ℕ
  | .native g => OriginalGroupedWordRAM.moveCharge X r f tau g
  | .chirp _ _ => 0
  | .affine _ _ _ => 0

def wordCharge (X : Layout α) (r f : ℕ) (tau : ℕ→ℕ) (p : Word α ρ) : ℕ :=
  (p.map (stepCharge X r f tau)).sum

theorem embed_charge (X : Layout α) (r f : ℕ) (tau : ℕ→ℕ)
    (p : OriginalGroupedFrameWords.Word α ρ) :
    wordCharge X r f tau (p.map Step.native)=OriginalGroupedWordRAM.wordCharge X r f tau p := by
  simp [wordCharge,OriginalGroupedWordRAM.wordCharge,List.map_map,Function.comp_def,stepCharge]
end Semantics

section Compiler
universe U
variable {α ρ : Type*} [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ] {ι : Type U}
  {m : Bool} {cl : Paint} {f : ι→ℕ} {s : Ty} {x : ι→T s}
  {X : Layout α} {R : Layout ρ} {r : ℕ}
  {v : ∀ i, Grain α ρ r (f i)}

theorem open_step (A : ρ → OBase α) (b : Bank (hatch cl) ι) (tau : ι→ℕ→ℕ)
    (Hframes : OriginalGroupedWordRAM.FrameService
      (m:=m) (f:=f) (X:=X) (R:=R) (r:=r) A b tau)
    (h : Rig m b.B f s x cl X R r v) (hr : 3≤X.n) (g : Step α ρ) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (ferry A r (f i) g (v i)))
      (fun i => (fleet X R r (f i)).n)
      (fun i => stepCharge X r (f i) (tau i) g) := by
  cases g with
  | native g =>
    simpa only [stepCharge,ferry,Step.go,OriginalGroupedWordRAM.ferry] using
      OriginalGroupedWordRAM.open_move A b tau Hframes h g
  | chirp l edges =>
    have H := Able.of_can (b:=b) (chirpData_native h hr l
      (fun j : Fin edges.length => edges.get j))
    simpa only [stepCharge,ferry,Step.go,chirpData] using H
  | affine l M z =>
    have H := Able.of_can (b:=b) (OriginalPhysicalAffineRAM.affineData_native h l M z)
    simpa only [stepCharge,ferry,Step.go,OriginalPhysicalAffineRAM.affineData] using H

/-- One emitted open RAM program; local constants pay all phase preparation
and routing. Every recursive call retains its exact additive coefficient. -/
theorem sweep (A : ρ → OBase α) (b : Bank (hatch cl) ι) (tau : ι→ℕ→ℕ)
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

/-- Instantiate every physical frame request through the existing complete
native kernel callback service, rather than a new spectral oracle. -/
theorem native_sweep (A : ρ → OBase α) (b : Bank (hatch cl) ι) (tau : ι→ℕ→ℕ)
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
end FourierSchur.OriginalContextualChirpWords
