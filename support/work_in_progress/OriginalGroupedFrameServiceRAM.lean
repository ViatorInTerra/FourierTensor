import work_in_progress.OriginalGroupedRoleResidualRAM
import work_in_progress.OriginalGroupedFrameFactorization

/-! The paid frame compiler uses one complete selected residual transform and
one paid address translation. It emits neither a Fourier sandwich nor dense
frame matrices. Empty residual masks emit no recursive calls. -/
namespace FourierSchur.OriginalGroupedFrameServiceRAM
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty Matrix Finset
open OriginalGroupedRoleResidualRAM OriginalGroupedFrameFactorization
open scoped BigOperators symmDiff
noncomputable section
universe U
variable {α ρ : Type*} [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ] {ι : Type U}
variable {m : Bool} {f : ι → Nat} {s : Ty} {x : ι → T s}
  {cl : Paint} {X : Layout α} {R : Layout ρ} {r : Nat}
  {v : ∀ i, Grain α ρ r (f i)}

def maskOp (A : OBase α) (S : Finset α) (r f : Nat)
    (v : Grid α r f → ℂ) : Grid α r f → ℂ :=
  fun q => matAct f (forwardMask A S) (fun j => v (q.1,j)) q.2

def frameOp (A : OBase α) (S T : Finset α) (r f : Nat)
    (v : Grid α r f → ℂ) : Grid α r f → ℂ :=
  fun q => matAct f (frame A T * unframe A S) (fun j => v (q.1,j)) q.2

theorem shift_mask_role (A : OBase α) (S T : Finset α) (r f : Nat)
    (l : ρ) (v : Grain α ρ r f) :
    OAI.PowerSaving.RAM.ferry r f (.shift l (correction A S T))
      (replaceRole l v (maskOp A (S ∆ T) r f (fun a => v (l,a)))) =
    replaceRole l v (frameOp A S T r f (fun a => v (l,a))) := by
  funext q
  by_cases hq : q.1=l
  · simp only [OAI.PowerSaving.RAM.ferry,OAI.PowerSaving.Binary.Move.go,
      roleAct,hq,ite_true,replaceRole,frameOp,maskOp]
    simpa using congrFun (amplified_ratio A S T f (fun j => v (l,q.2.1,j))) q.2.2 |>.symm
  · simp [OAI.PowerSaving.RAM.ferry,OAI.PowerSaving.Binary.Move.go,
      roleAct,hq,replaceRole]

/-- One physical frame ratio, preserving all other arbitrary role banks. -/
theorem frame_role_from_raw (b : Bank (hatch cl) ι)
    (h : Rig m b.B f s x cl X R r v) (l : ρ)
    (A : OBase α) (S T : Finset α) (Z : ι → Nat)
    (Hraw : Able m b (simIn cl) (bundle cl)
      (fun i => GroupedResidual.givenGrid cl X r (f i) (fun a => v i (l,a)))
      (fun i => (book X r (f i)).tape
        (maskOp A (S ∆ T) r (f i) (fun a => v i (l,a))))
      (fun i => (book X r (f i)).n) Z) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape
        (replaceRole l (v i) (frameOp A S T r (f i) (fun a => v i (l,a)))))
      (fun i => (fleet X R r (f i)).n) Z := by
  let v' i := replaceRole l (v i)
    (maskOp A (S ∆ T) r (f i) (fun a => v i (l,a)))
  have HR := embed_open b h l _ Z Hraw
  let env i : Ty.T (p s (bundle cl)) := (x i,(fleet X R r (f i)).tape (v' i))
  have hg := h.gather id env (t:=p s (bundle cl)) Can.first
  have next : Rig m b.B f (p s (bundle cl)) env cl X R r v' :=
    ⟨hg.gear,hg.imag,Can.second⟩
  have HS := Able.of_can (b:=b) (next.shift_cost l (correction A S T))
  have H := HR.save_keep HS
  simpa only [Nat.add_zero,v',shift_mask_role] using H

theorem frameOp_self (A : OBase α) (S : Finset α) (r f : Nat)
    (v : Grid α r f → ℂ) : frameOp A S S r f v=v := by
  funext q
  simp [frameOp,unframe_right]

theorem rank_eq (S T : ρ → Finset α) (l : ρ) :
    OriginalGroupedWordRAM.residualRank S T l = ((S l) ∆ (T l)).card := rfl

end
end FourierSchur.OriginalGroupedFrameServiceRAM
