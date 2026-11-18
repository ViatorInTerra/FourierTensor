import work_in_progress.OriginalGroupedFrameServiceRAM
import work_in_progress.OriginalGroupedResidualSemantics

/-! Actual frame-service instantiation. The sole external interface is the
native raw recursive-call contract, for strictly smaller selected tensor
orders supplied by the enclosing recursive body. All other work is compiled. -/
namespace FourierSchur.OriginalGroupedFrameCompilerRAM
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty Matrix Finset
open OriginalGroupedWordRAM OriginalGroupedRoleResidualRAM OriginalGroupedFrameServiceRAM
open scoped BigOperators symmDiff
noncomputable section
universe U
variable {α ρ : Type*} [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ] {ι : Type U}

theorem frame_service (cl : Paint) (m : Bool)
    (X : Layout α) (R : Layout ρ) (r : Nat) (hr : 3≤X.n)
    (f : ι → Nat) (A : ρ → OBase α)
    (b : Bank (hatch cl) ι) (tau : ι → Nat → Nat)
    (HC : ∀ n : Nat, 0<n → n≤X.n → GroupedResidual.Rig.RawContract cl b
      (fun i => n*f i) (fun i => tau i (n*f i))) :
    FrameService (m:=m) (f:=f) (X:=X) (R:=R) (r:=r) A b tau := by
  intro s x v h S T
  let op fi l := frameOp (A l) (S l) (T l) r fi
  let charge l i := if residualRank S T l=0 then 0 else
    (2^r * (2^f i)^(X.n-residualRank S T l)) * (tau i (residualRank S T l*f i))
  have HS : RoleService (m:=m) (f:=f) (X:=X) (R:=R) (r:=r) b op charge := by
    intro s x v h l
    by_cases hz : residualRank S T l=0
    · have he : S l=T l := by
        apply Finset.symmDiff_eq_empty.mp
        apply Finset.card_eq_zero.mp
        simpa only [← rank_eq] using hz
      have Hout (i) : replaceRole l (v i)
          (op (f i) l (fun a => v i (l,a))) = v i := by
        dsimp [op]
        rw [he,frameOp_self]
        funext q
        by_cases hq : q.1=l
        · simp only [replaceRole,hq,ite_true]
          exact congrArg (v i) (Prod.ext hq.symm rfl)
        · simp [replaceRole,hq]
      have H := (Able.of_can (b:=b) (h.items.mono
        (W':=fun i => (fleet X R r (f i)).n) (fun _ => Nat.zero_le _))).cong
          (fun _ => rfl) (fun i => congrArg (fleet X R r (f i)).tape (Hout i).symm)
      simpa only [charge,hz,ite_true] using H
    · let U : Finset α := (S l) ∆ (T l)
      let Y := Layout.someLayout {j : α // j∈U}
      let Z := Layout.someLayout {j : α // j∉U}
      let e := GroupedResidual.ColumnRoute.forSubset (A l) U
      have hy : Y.n=residualRank S T l := by
        rw [← Y.card,Fintype.card_coe]
        exact (rank_eq S T l).symm
      have hdim : X.n=Y.n+Z.n := by
        rw [← X.card,← Y.card,← Z.card]
        exact e.card_eq
      have hn : 0<residualRank S T l := Nat.pos_of_ne_zero hz
      have hle : residualRank S T l≤X.n := by omega
      have hc : GroupedResidual.Rig.RawContract cl b (fun i => Y.n*f i)
          (fun i => tau i (Y.n*f i)) := by
        simpa only [hy] using HC _ hn hle
      have Hraw := GroupedResidual.run_open_grid (m:=m) (e:=e) (X:=X) (Y:=Y) (Z:=Z)
        (r:=r) (f:=f) (v:=fun i a => v i (l,a))
        b (fun i => tau i (Y.n*f i)) hr (h.gear.grid_small X r) hc
      have Hout (i) : (book X r (f i)).tape
          (GroupedResidual.result e Y r (f i) (fun a => v i (l,a))) =
          (book X r (f i)).tape (maskOp (A l) U r (f i) (fun a => v i (l,a))) := by
        congr 1
        funext q
        exact GroupedResidual.result_eq_forwardMask (A l) U Y r (f i)
          (fun a => v i (l,a)) q.1 q.2
      have H := frame_role_from_raw b h l (A l) (S l) (T l)
        (fun i => (book Z r (f i)).n*tau i (Y.n*f i))
        (Hraw.cong (fun _ => rfl) Hout)
      have hzc : Z.n=X.n-residualRank S T l := by omega
      have Hcost : (fun i => (book Z r (f i)).n*tau i (Y.n*f i))=charge l := by
        funext i
        dsimp [charge]
        rw [if_neg hz,hy]
        change (2^r*(2^f i)^Z.n)*tau i (residualRank S T l*f i)=_
        rw [hzc]
      simpa only [op,Hcost] using H
  have H := all_roles b op charge HS h
  simpa only [op,charge,frameCharge,OriginalGroupedWordRAM.ferry,
    OriginalGroupedFrameWords.Move.go,multiAct,frameOp] using H

end
end FourierSchur.OriginalGroupedFrameCompilerRAM
