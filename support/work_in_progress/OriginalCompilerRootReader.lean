import work_in_progress.OriginalCompilerRootPreparation
import work_in_progress.OriginalSectorSubstitution

/-! Actual shared parent-root access for the parameterized tensor executor.
The reader is constructed from the retained finite RAM array; it is not a
reader assumption.  Joint construction of that array is charged by
`OriginalCompilerRootPreparation.rootTable_dry`.  No faster tensor executor
or global density estimate is instantiated here. -/

namespace FourierSchur.OriginalCompilerRootReader
open OAI.PowerSaving OAI.PowerSaving.Selection OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty OAI.PowerSaving.RAM.Bench
open OriginalCompilerRootBridge OriginalCompilerRootPreparation
open OriginalSectorSubstitution
noncomputable section
universe U

variable {m : Bool} {ι : Type U} {b : OAI.PowerSaving.RAM.Bench m ι}
  {S n W : ι → ℕ}

/-- A single constant-work RAM reader, uniform over all permitted requests.
The `Small` hypothesis controls the requested integer register as well as
the integer words produced by the ordinary array lookup. -/
theorem rootTable_TableReader
    (ht : b.Moves (fun _ => 0) (a sc) (fun i => rootTable (n i)))
    (hl : Small b.size (fun i => (barge (n i)).l)) :
    TableReader b (fun i => (barge (n i)).l) sc parentRoot := by
  let J := Σ i : ι, Fin ((barge (n i)).l+1)
  let base := b.along (fun j : J => j.1)
  let k : J → ℕ := fun j => j.2.val
  let D := base.extend w k
  have F : D.Instant b (fun j : J => j.1) :=
    (Instant.extend base k (t:=w)).next (Instant.along b (fun j : J => j.1))
  have hk : D.Nick k :=
    ⟨cherry base k (t:=w) (W:=fun _ => 0),
      (hl.reindex (fun j : J => j.1)).mono
        (fun j => Nat.le_of_lt_succ j.2.isLt)⟩
  change D.Moves (fun _ => 0) sc (fun j => parentRoot (k j))
  exact rootTable_reader (ht.transfer F) hk
    (fun j => Nat.le_of_lt_succ j.2.isLt)

/-- Retaining the once-prepared array in an ordinary environment register
provides all parent-root reads required by the sector substitution theorem. -/
theorem retainedRootTable_TableReader
    (hl : Small b.size (fun i => (barge (n i)).l)) :
    TableReader (b.extend (a sc) (fun i => rootTable (n i)))
      (fun i => (barge (n i)).l) sc parentRoot :=
  rootTable_TableReader
    (cherry b (fun (i : ι) => rootTable (n i)) (t:=a sc) (W:=fun _ => 0)) hl

/-- Charge joint table preparation once, then execute in the environment
that retains the prepared array. The polynomial integer cap remains within
the same `Can` certificate throughout this composition. -/
theorem pay_rootTable {u : Ty} {y : ι → T u}
    (hp : b.Dry S (a sc) (fun i => rootTable (n i)))
    (hy : (b.extend (a sc) (fun i => rootTable (n i))).Moves W u y) :
    ∃ d : ℕ, b.Moves (fun i => W i+(S i+2)^d) u y := by
  obtain ⟨d,hd⟩ := hp
  refine ⟨d,caseM (t:=a sc) (x:=fun (i : ι) => rootTable (n i)) ?_ ?_⟩
  · exact hd.mono (fun i => Nat.le_add_left _ _)
  · exact hy.weaken (Dom.of_le (fun i => Nat.le_add_right _ _))

/-- The actual upstream supplied-root preparation followed by any consumer
of the constructed parent-root reader. The consumer receives the proved
reader certificate; it need not hypothesize an oracle or fresh root tables. -/
theorem with_paid_parentRoot_reader {z : ι → ℂ} {u : Ty} {y : ι → T u}
    (h : b.Neaps S n) (hports : ∀ i, Ports (n i))
    (hz : b.Dry S sc z)
    (hreceipt : b.Dry S sc (fun i => root (receipt (n i))))
    (hy : TableReader (b.extend (a sc) (fun i => rootTable (n i)))
        (fun i => (barge (n i)).l) sc parentRoot →
      (b.extend (a sc) (fun i => rootTable (n i))).Moves W u y) :
    ∃ d : ℕ, b.Moves (fun i => W i+(S i+2)^d) u y := by
  have hl : Small b.size (fun i => (barge (n i)).l) :=
    h.bargeL.countS.trans h.tidal.small
  exact pay_rootTable (rootTable_dry h hports hz hreceipt)
    (hy (retainedRootTable_TableReader hl))

end
end FourierSchur.OriginalCompilerRootReader
