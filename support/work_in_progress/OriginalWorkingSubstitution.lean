import work_in_progress.OriginalCompilerRootReader
import work_in_progress.OriginalSynchronizedSubstitution

/-! Working-length Fourier compilation with a supplied complete tensor
executor. Parent-root access is proved from a retained, once-prepared array,
and its joint preparation is charged through the original supplied receipt
root. The remaining tensor executor hypothesis is a genuine uniform `Can`
certificate on arbitrary input vectors; no faster density is instantiated. -/

namespace FourierSchur.OriginalWorkingSubstitution
open OAI.PowerSaving OAI.PowerSaving.Selection OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty OAI.PowerSaving.RAM.Bench
open Grove Slant Spectral
open OriginalCompilerRootBridge OriginalCompilerRootPreparation
open OriginalCompilerRootReader OriginalSectorSubstitution
noncomputable section
universe U

/-- Online work, including local synchronized layers and all routing. -/
def leg (t : ℕ → ℕ) (n : ℕ) : ℕ :=
  (score (orderE n)+1)*((barge n).vol*(t (barge n).l+1))

variable {m : Bool} {ι : Type U} {b : OAI.PowerSaving.RAM.Bench m ι}
  {n S : ι → ℕ} {t : ℕ → ℕ} {z : ι → ℂ} {cl : Paint} {x : ι → Line}

private theorem streamP_with_parentRoot_reader
    (hExec : SuppliedTensorExecutor sc parentRoot cl m t) (hmono : Monotone t)
    (hRead : TableReader b (fun i => (barge (n i)).l) sc parentRoot)
    (h : b.Neaps S n) (g : ∀ i, Ports (n i))
    (hz : b.Dry S sc (fun i => root (receipt (n i))))
    (hu : b.Dry S sc z)
    (hp : ∀ i, IsPrimitiveRoot (z i) (barge (n i)).vol)
    (hx : b.Moves (fun _ => 0) (a (c cl)) (fun i =>
      Tape.tab (barge (n i)).vol (x i))) :
    ∃ d : ℕ, b.Moves (fun i => leg t (n i)+(S i+2)^d)
      (a (c cl)) (fun i => Tape.tab (barge (n i)).vol
        (freq (barge (n i)).vol (z i) (x i))) := by
  let X i := barge (n i)
  have hX i := barge_spec (n i) (h.pos i)
  have he i : (X i).vol=extent (X i).q (X i).l := (hX i).square.agrees
  let forgeData i := forge (X i).l (orderE (n i)) (X i).q (z i)
  have F := Instant.extend b forgeData (t:=forgeTy)
  have hr := hRead.transfer F
  have hh := OriginalSynchronizedSubstitution.Bench.effuse_supplied
    hExec hmono hr (r:=fun i => (X i).q) (l:=fun i => (X i).l)
    (e:=fun i => orderE (n i)) (z:=z) (b:=b) (x:=x)
    (fun i => (hX i).square.isles) (fun i => (hX i).sizes)
    (fun i => he i ▸ hp i) h.bargeL.countS h.powOrderS h.tidal.small
    (h.bargeL.volume.mono (fun i => (he i).symm.le))
    (h.kilnP g hu hz)
    (hx.congr (fun i => congrArg (fun d => Tape.tab d (x i)) (he i)))
  obtain ⟨d,hd⟩ := hh
  refine ⟨d,(hd.weaken (Dom.of_le (fun i => ?_))).congr (fun i => ?_)⟩
  · simp only [leg,← he]
    exact le_rfl
  · simp only [← he,X]

/-- The actual `Neaps.streamP` boundary with a replaceable complete tensor
executor. The parent-root reader is constructed, and its polynomial joint
preparation is paid once. The resulting `Moves` includes both operation
bounds and a polynomial cap on every produced integer. -/
theorem streamP_supplied
    (hExec : SuppliedTensorExecutor sc parentRoot cl m t) (hmono : Monotone t)
    (h : b.Neaps S n) (g : ∀ i, Ports (n i))
    (hz : b.Dry S sc (fun i => root (receipt (n i))))
    (hu : b.Dry S sc z)
    (hp : ∀ i, IsPrimitiveRoot (z i) (barge (n i)).vol)
    (hx : b.Moves (fun _ => 0) (a (c cl)) (fun i =>
      Tape.tab (barge (n i)).vol (x i))) :
    ∃ d : ℕ, b.Moves (fun i => leg t (n i)+(S i+2)^d)
      (a (c cl)) (fun i => Tape.tab (barge (n i)).vol
        (freq (barge (n i)).vol (z i) (x i))) := by
  let D := b.extend (a sc) (fun i => rootTable (n i))
  have F := Instant.extend b (fun i => rootTable (n i)) (t:=a sc)
  have hl : Small b.size (fun i => (barge (n i)).l) :=
    h.bargeL.countS.trans h.tidal.small
  have hRead : TableReader D (fun i => (barge (n i)).l) sc parentRoot :=
    retainedRootTable_TableReader hl
  obtain ⟨a,ha⟩ := streamP_with_parentRoot_reader hExec hmono hRead
    (h.transfer F) g (hz.transfer F) (hu.transfer F) hp (hx.transfer F)
  obtain ⟨d,hd⟩ := with_paid_parentRoot_reader
    (W:=fun i => leg t (n i)+(S i+2)^a) h g hu hz (fun _ => ha)
  refine ⟨a+d,hd.weaken ?_⟩
  refine ⟨2,fun i => ?_⟩
  have hA : (S i+2)^a ≤ (S i+2)^(a+d) :=
    Small.pow_mono_degree (S i) (show a ≤ a+d by omega)
  have hD : (S i+2)^d ≤ (S i+2)^(a+d) :=
    Small.pow_mono_degree (S i) (show d ≤ a+d by omega)
  change (leg t (n i)+(S i+2)^a)+(S i+2)^d+1 ≤
    2*(leg t (n i)+(S i+2)^(a+d)+1)
  omega

end
end FourierSchur.OriginalWorkingSubstitution
