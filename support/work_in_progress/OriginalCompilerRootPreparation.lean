import work_in_progress.OriginalCompilerRootBridge

/-! Paid joint preparation of the Schur parent roots from the actual
all-length Fourier forge.  The resulting finite table supports ordinary
constant-work indexed RAM reads.  Scalar/route preparation for the complete
Schur executor and the global density bound are separate obligations. -/
namespace FourierSchur.OriginalCompilerRootPreparation
open OriginalCompilerRootBridge ToeplitzSuppliedRoots
open OAI.PowerSaving OAI.PowerSaving.Selection OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty OAI.PowerSaving.RAM.Bench
noncomputable section
universe U

def rootTable (n : Nat) : OAI.PowerSaving.Tape ℂ :=
  OAI.PowerSaving.Tape.tab ((barge n).l+1) parentRoot

theorem rootTable_length (n : Nat) : (rootTable n).len=(barge n).l+1 := rfl

theorem rootTable_lookup (n k : Nat) (hk : k≤(barge n).l) :
    (rootTable n).look k 0=parentRoot k := by
  rw [rootTable,OAI.PowerSaving.Tape.look_tab,
    if_pos (show k<(barge n).l+1 by omega)]

variable {m : Bool} {ι : Type U} {b : Bench m ι}
  {S n k : ι→Nat}

theorem parentExponent_grain (hk : b.Grain S k) (hks : Small S k) :
    b.Grain S (fun i => parentExponent (capacity (k i))) := by
  have hp := hk.add (Grain.wc 1)
  have hc : b.Grain S (fun i => capacity (k i)) :=
    (hp.mul hp).congr (fun i => by simp only [capacity,pow_two])
  have hcs : Small S (fun i => capacity (k i)) :=
    (hks.add (Small.const _ 1)).pow 2
  simpa only [parentExponent,Nat.log2_eq_log_two] using
    (hc.logtwo hcs).add (Grain.wc 2)

theorem parentRoot_dry_from_forge (h : b.Neaps S n)
    {z : ι→ℂ}
    (hf : b.Dry S forgeTy (fun i =>
      forge (barge (n i)).l (orderE (n i)) (barge (n i)).q (z i)))
    (hk : b.Grain S k) (hks : Small S k)
    (hkl : ∀ i,k i≤(barge (n i)).l) :
    b.Dry S sc (fun i => parentRoot (k i)) := by
  have he := parentExponent_grain hk hks
  have halosPrepared : b.Dry S (a sc) (fun i =>
      OAI.PowerSaving.Tape.tab (orderE (n i)+1) halos) :=
    hf.snd.snd.snd.snd.fst
  exact (Dry.pick (n:=fun i => orderE (n i)+1)
    (k:=fun i => parentExponent (capacity (k i))) halosPrepared he.dry
    (fun i => by
      change parentExponent (capacity (k i)) < orderE (n i)+1
      have hh := parentExponent_le_order (n i) (k i) (h.pos i) (hkl i)
      omega)).congr (fun _ => rfl)

theorem rootTable_dry_from_forge (h : b.Neaps S n)
    {z : ι→ℂ}
    (hf : b.Dry S forgeTy (fun i =>
      forge (barge (n i)).l (orderE (n i)) (barge (n i)).q (z i))) :
    b.Dry S (a sc) (fun i => rootTable (n i)) := by
  let L i := (barge (n i)).l+1
  have hl : b.Grain S L := h.bargeL.dimL.add (Grain.wc 1)
  have hls : Small S L := h.bargeL.countS.add (Small.const _ 1)
  have F := Instant.scan b L
  have hk := chopG hl
  have hks : Small (fun d : During L => S d.i) (fun d => d.j) :=
    (hls.reindex During.i).mono (fun d => d.hj.le)
  have hx : (b.scan L).Dry (fun d => S d.i) sc (fun d => parentRoot d.j) :=
    parentRoot_dry_from_forge (h.transfer F) (hf.transfer F) hk hks
      (fun d => by have hh := d.hj; dsimp only [L] at hh; omega)
  exact arrayG (t:=sc) hl hls (fun (_ : ι) (j : Nat) => parentRoot j) hx

/-- The forge is constructed by the upstream paid scalar program, including
extraction of all dyadic halos from the supplied root of receipt(n). -/
theorem rootTable_dry (h : b.Neaps S n) (hports : ∀ i,Ports (n i))
    {z : ι→ℂ} (hz : b.Dry S sc z)
    (hreceipt : b.Dry S sc (fun i => root (receipt (n i)))) :
    b.Dry S (a sc) (fun i => rootTable (n i)) :=
  rootTable_dry_from_forge h (h.kilnP hports hz hreceipt)

/-- Once the paid finite table is retained in the environment, an ordinary
RAM array lookup retrieves the parent root in constant work. -/
theorem rootTable_reader
    (ht : b.Moves (fun _ => 0) (a sc) (fun i => rootTable (n i)))
    (hk : b.Nick k) (hkl : ∀ i,k i≤(barge (n i)).l) :
    b.Moves (fun _ => 0) sc (fun i => parentRoot (k i)) :=
  Moves.pick (t:=sc) (n:=fun i => (barge (n i)).l+1)
    (fun (_ : ι) (j : Nat) => parentRoot j) ht hk.close (fun i => by
      change k i < (barge (n i)).l+1
      have hh := hkl i
      omega)

theorem rootTable_lookup_primitive (n k : Nat) (hk : k≤(barge n).l) :
    IsPrimitiveRoot ((rootTable n).look k 0) (2^(parentExponent (capacity k))) := by
  rw [rootTable_lookup n k hk]
  exact parentRoot_primitive k

end
end FourierSchur.OriginalCompilerRootPreparation
