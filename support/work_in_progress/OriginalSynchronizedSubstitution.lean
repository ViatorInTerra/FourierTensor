import work_in_progress.OriginalSectorSubstitution

/-! Synchronized Fourier executor substitution, conditional on an executable
complete supplied tensor program and actual constant-work access to its shared
preparation registers. All packing, monomial layers, repetition and CRT routing
are charged by the original RAM semantics. This file does not construct the
shared preparation or instantiate a fast tensor-density certificate. -/

namespace FourierSchur.OriginalSynchronizedSubstitution
open OAI OAI.PowerSaving OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty OAI.PowerSaving.RAM.Bench
open Finset Grove Slant Spectral
open FourierSchur.OriginalSectorSubstitution
noncomputable section
universe U
namespace Bench
variable {m : Bool} {ι : Type U} {b : OAI.PowerSaving.RAM.Bench m ι}
  {cl : Paint} {l d : ι → ℕ} {r : ι → Axes} {x : ι → Line}
  {t : ℕ → ℕ} {s : Ty} {table : ℕ → T s}

section StrokeLayers
variable {u : ι → ℕ → Stroke}
namespace Bough

theorem water_supplied (hExec : SuppliedTensorExecutor s table cl m t) (hmono : Monotone t) (hRead : TableReader b l s table) (h : b.Bough l r u) (hI : b.Moves (fun _ => 0) sc fun _ => Complex.I)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (extent (r i) (l i)) (x i)) :
    b.Moves (fun i => extent (r i) (l i)*(t (l i)+1)) (a (c cl)) fun i =>
      Tape.tab (extent (r i) (l i))
        (graft (extent (r i) (l i)) (canopy (r i) (fun j => leafC (u i j)) (l i)) (x i)) := by
  let n i := extent (r i) (l i)
  let V i := mosaic (r i) (u i) (l i)
  let Y i := upholstery (n i) (V i)
  let D := b.extend (a chipTy) Y
  have F := Instant.extend b Y (t:=a chipTy)
  have hn : b.Nick n := ⟨hx.len h.fen.span,h.fen.span⟩
  have he : D.Matting n l V :=
    ⟨hn.transfer F,fun i => mosaic_quilt _ _ _ (h.fen.good i) (h.good i),
      cherry b Y (t:=a chipTy)⟩
  have hd : Dom (fun i => n i*(t (l i)+1)) n :=
    Dom.of_le (fun i => Nat.le_mul_of_pos_right _ (Nat.succ_pos (t (l i))))
  have ht := caseM (h.bedding.weaken hd) (OriginalSectorSubstitution.Bench.Matting.cardT_supplied_executor hExec hmono (hRead.transfer F) he (hx.transfer F) (hI.transfer F))
  exact ht.congr fun i => tapeCongr (n i) _ _ fun j hj =>
    (graft_glimpse _ _ _ (h.fen.good i) (h.good i) _ _ hj).symm

theorem swell_supplied (hExec : SuppliedTensorExecutor s table cl m t) (hmono : Monotone t) (hRead : TableReader b l s table) (h : b.Bough l r u) (hI : b.Moves (fun _ => 0) sc fun _ => Complex.I)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (extent (r i) (l i)) (x i)) :
    b.Moves (fun i => extent (r i) (l i)*(t (l i)+1)) (a (c cl)) fun i =>
      Tape.tab (extent (r i) (l i))
        (graft (extent (r i) (l i)) (canopy (r i) (fun j => leafC (u i j)) (l i))
          (graft (extent (r i) (l i)) (canopy (r i) (fun j => leafM (u i j)) (l i))
            (x i))) := by
  let n i := extent (r i) (l i)
  let f i := graft (n i) (canopy (r i) (fun j => leafM (u i j)) (l i)) (x i)
  let y i := Tape.tab (n i) (f i)
  let D := b.extend (a (c cl)) y
  have F := Instant.extend b y (t:=a (c cl))
  have ht := water_supplied hExec hmono (hRead.transfer F) (h.transfer F) (x:=f) (hI.transfer F)
    (cherry b y (t:=a (c cl)))
  exact caseM ((h.glean cl x hx).weaken (Dom.of_le (fun i => Nat.le_mul_of_pos_right _
    (Nat.succ_pos (t (l i)))))) ht
end Bough
end StrokeLayers

section ReelTrees
variable {pV : ι → ℕ → Reel}
namespace Thicket
/-- Run synchronized transform. Input tape in mixed-radix order, output likewise. -/
theorem conduct_supplied (hExec : SuppliedTensorExecutor s table cl m t) (hmono : Monotone t) (hRead : TableReader b l s table) (h : b.Thicket l d r pV) (hI : b.Moves (fun _ => 0) sc fun _ => Complex.I)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (extent (r i) (l i)) (x i)) :
    b.Moves (fun i => d i* (extent (r i) (l i)*(t (l i)+1)))
      (a (c cl)) fun i => Tape.tab (extent (r i) (l i))
        (forest (r i) (l i) (pV i) (x i) (d i)) := by
  let n i := extent (r i) (l i)
  let T i := forest (r i) (l i) (pV i) (x i)
  let A i j := Tape.tab (n i) (T i j)
  have F := Instant.climbs b d (t:=a (c cl)) A
  have ht := (h.transfer F).digitize (stride h.beats (t:=a (c cl)) A) During.hj
  have he := Bough.swell_supplied hExec hmono (hRead.transfer F) ht (x:=fun i => T i.i i.j) (hI.transfer F) (tokenNow b d (t:=a (c cl)) A)
  have hu := repeatM h.beats A hx he (u:=fun i _ => n i*(t (l i)+1)) (t:=a (c cl))
  refine hu.weaken ?_
  refine ⟨2,fun i => ?_⟩
  have hh : d i ≤ d i*(extent (r i) (l i)*(t (l i)+1)) :=
    Nat.le_mul_of_pos_right (d i) (Nat.mul_pos (h.fen.good i).extent_pos
      (Nat.succ_pos (t (l i))))
  simp only [sum_const,card_range,smul_eq_mul]
  unfold n
  omega

theorem stream_supplied (hExec : SuppliedTensorExecutor s table cl m t) (hmono : Monotone t) (hRead : TableReader b l s table) (h : b.Thicket l d r pV) (hI : b.Moves (fun _ => 0) sc fun _ => Complex.I)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (extent (r i) (l i)) (x i))
    (X : ι→ℕ→Wood) (hg : ∀ i, ∀ j<l i, Creates (pV i j) (r i j) (Grove.frame _ (X i j))) :
    b.Moves (fun i => d i*(extent (r i) (l i)*(t (l i)+1)))
      (a (c cl)) fun i => Tape.tab (extent (r i) (l i))
        (graft (extent (r i) (l i)) (canopy (r i) (X i) (l i)) (x i)) :=
  (conduct_supplied hExec hmono hRead h hI hx).congr fun i =>
    tapeCongr _ _ _ fun j hj => forest_completes (r i) (l i) (pV i) (h.fen.good i)
      (d i) (h.sounds i) (h.length i) (X i) (hg i) (x i) j hj

end Thicket
end ReelTrees

section WorkingFourier
variable {u : ι → ℕ → Reel}
namespace Thicket
variable {z : ι → ℂ}

private lemma via_supplied (hExec : SuppliedTensorExecutor s table cl m t) (hmono : Monotone t) (hRead : TableReader b l s table) (h : b.Thicket l d r u) (hh : ∀ i, Isles (r i) (l i))
    (hz : ∀ i, IsPrimitiveRoot (z i) (extent (r i) (l i)))
    (hg : ∀ i, ∀ j<l i, Creates (u i j) (r i j)
      (winds _ (spray (z i) (extent (r i) (l i)) (r i j))))
    (hI : b.Moves (fun _ => 0) sc fun _ => Complex.I)
    (hF : b.Moves (fun _ => 0) (a dualWord) fun i =>
      Tape.tab (extent (r i) (l i)) (chart (r i) (l i)))
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (extent (r i) (l i)) (x i)) :
    b.Moves (fun i => (d i+1)*(extent (r i) (l i)*(t (l i)+1))) (a (c cl))
      fun i => Tape.tab (extent (r i) (l i)) (freq (extent (r i) (l i)) (z i) (x i)) := by
  let n i := extent (r i) (l i)
  let W i := (d i+1)*(n i*(t (l i)+1))
  let C i := ford (r i) (l i)
  let y i j := x i (C i j)
  let A i := Tape.tab (n i) (y i)
  let V i := freq (n i) (z i) (x i)
  let Z i := Tape.tab (n i) fun j => V i (C i j)
  let M i := fun j => gale (spray (z i) (n i) (r i j))
  have H : Dom W n := Dom.of_le fun i => le_trans (Nat.le_mul_of_pos_right _
    (Nat.succ_pos (t (l i)))) (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  have hn : b.Nick n := ⟨hx.len h.fen.span,h.fen.span⟩
  have hhC i : Reloc (n i) (C i) := ford_rel (hh i)
  have hp := chop hn
  have F := Instant.scan b n
  have hc := (Moves.pick (t:=dualWord) (n:=fun i : During n => n i.i) _ (hF.transfer F) hp.close During.hj).snd
  have hy : b.Moves W (a (c cl)) A := by
    have hx' := Moves.pick (t:=c cl) (n:=fun i : During n => n i.i)
      (fun i => x i.i) (hx.transfer F) hc (fun i => (hhC i.i).bd _ i.hj)
    exact (arrayNow (t:=c cl) hn y hx').weaken H
  have hz' : b.Moves W (a (c cl)) Z := by
    let D := b.extend (a (c cl)) A
    have G := Instant.extend b A (t:=a (c cl))
    have ht := stream_supplied hExec hmono (hRead.transfer G) (h.transfer G) (x:=y) (hI.transfer G) (cherry b A (t:=a (c cl))) M hg
    refine caseM hy ((ht.congr ?_).weaken ?_)
    · intro i
      exact tapeCongr (n i) _ _ fun j hj => graft_ford (hh _) (hz _) _ j hj
    · exact Dom.of_le (fun i => Nat.mul_le_mul_right (n i*(t (l i)+1)) (Nat.le_succ (d i)))
  let B := b.extend (a (c cl)) Z
  have G := Instant.extend b (t:=a (c cl)) Z
  have he : B.Nick n := hn.transfer G
  have I1 := Instant.scan B n
  have I2 : (B.scan n).Instant (b.scan n) id :=
    Instant.select (I1.next G) (chop he).close
  have ht := Moves.pick (b:=B.scan n) (t:=c cl) (n:=fun i => n i.i) (fun i j => V i.i (C i.i j))
    ((cherry b Z (W:=fun _=>0) (t:=a (c cl))).transfer I1) (chop he).close During.hj
  have hg' := scatterNow (t:=c cl) he (fun i j => (C i j,V i (C i j))) ((hc.transfer I2).pair ht)
  refine caseM hz' ((hg'.weaken H).congr ?_)
  intro i; rw [(hhC i).sow (fun j => V i (C i j)) _]
  exact tapeCongr (n i) _ _ fun j hj => congr_arg (V i) ((hhC i).seeks hj).2

theorem traverse_supplied (hExec : SuppliedTensorExecutor s table cl m t) (hmono : Monotone t) (hRead : TableReader b l s table) (h : b.Thicket l d r u) (hh : ∀ i, Isles (r i) (l i))
    (hz : ∀ i, IsPrimitiveRoot (z i) (extent (r i) (l i)))
    (hg : ∀ i, ∀ j<l i, Creates (u i j) (r i j)
      (winds _ (spray (z i) (extent (r i) (l i)) (r i j))))
    (hI : b.Moves (fun _ => 0) sc fun _ => Complex.I)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (extent (r i) (l i)) (x i)) :
    b.Moves (fun i => (d i+1)*(extent (r i) (l i)*(t (l i)+1))) (a (c cl))
      fun i => Tape.tab (extent (r i) (l i)) (freq (extent (r i) (l i)) (z i) (x i)) := by
  let n i := extent (r i) (l i)
  let A i := Tape.tab (n i) (chart (r i) (l i))
  have F := Instant.extend b A (t:=a dualWord)
  have ht := via_supplied hExec hmono (hRead.transfer F) (h.transfer F) (z:=z) hh hz hg
    (hI.transfer F) (cherry b A (t:=a dualWord)) (x:=x) (hx.transfer F)
  refine caseM ((h.fen.chartT hh).weaken ?_) ht
  exact Dom.of_le fun i => le_trans (Nat.le_mul_of_pos_right (n i)
    (Nat.succ_pos (t (l i)))) (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))

end Thicket
end WorkingFourier
/- Preparation is charged by the original polynomial `forge` and `kiln`
certificates. The reader hypothesis requires the executor registers to be
available from that materialized forge; it does not establish new tables. -/
section PreparedWorkingFourier
variable {e S : ι → ℕ} {z : ι → ℂ}

theorem effuse_supplied (hExec : SuppliedTensorExecutor s table cl m t) (hmono : Monotone t)
    (hRead : TableReader (b.extend forgeTy (fun i => forge (l i) (e i) (r i) (z i))) l s table)
    (h : ∀ i, Isles (r i) (l i)) (hl : ∀ i, ∀ j<l i, r i j≤2^e i)
    (hz : ∀ i, IsPrimitiveRoot (z i) (extent (r i) (l i)))
    (h1 : Small S l) (h2 : Small S fun i => 2^e i)
    (h3 : Small b.size S) (h4 : Small b.size fun i => extent (r i) (l i))
    (hp : PolyCan m b.size S b.tray forgeTy b.env fun i => forge (l i) (e i) (r i) (z i))
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (extent (r i) (l i)) (x i)) :
    ∃ d : ℕ,
    b.Moves (fun i => (score (e i)+1)*(extent (r i) (l i)*(t (l i)+1)) + (S i+2)^d)
      (a (c cl)) fun i => Tape.tab (extent (r i) (l i))
        (freq (extent (r i) (l i)) (z i) (x i)) := by
  let n i := extent (r i) (l i)
  let f i := forge (l i) (e i) (r i) (z i)
  let D := b.extend forgeTy f
  let q : OAI.PowerSaving.RAM.Bench m ι := ⟨S,D.tray,D.env⟩
  have F0 := Instant.extend b f
  have Hq : q.Foundry r l e z :=
    ⟨h,hl,hz,h1,h2,cherry (OAI.PowerSaving.RAM.Bench.mk (m:=m) S b.tray b.env) f (t:=forgeTy)⟩
  have H : D.Foundry r l e z := Hq.transfer (f:=id) (show D.Instant q id from
    ⟨envNow D,h3⟩)
  obtain ⟨d,hd⟩ := hp
  obtain ⟨a,hA⟩ := Hq.kilnD
  let V i := kiln (r i) (l i) (e i) (z i)
  let K := D.extend kilnTy V
  have F := Instant.extend D V (t:=kilnTy)
  have ht := (H.transfer F).table (hn:=h4) (cherry D V (t:=kilnTy))
  let R i := (score (e i)+1)*(n i*(t (l i)+1))
  let W i := R i+(S i+2)^(d+a)
  have hr : K.Moves R (Ty.a (c cl)) fun i => Tape.tab (n i) (freq (n i) (z i) (x i)) :=
    Thicket.traverse_supplied hExec hmono (hRead.transfer F) ht h hz (fun i j hj => creates_ballad _ _ _ _ (hl i j hj) (haloSprings _)
      (spray_axis (h _) (hz i) _ hj)) (H.unitM.transfer F) (hx.transfer (F.next F0))
  have hd' : b.Moves W forgeTy f := hd.mono (fun i => le_trans
    (Small.pow_mono_degree _ (show d≤d+a by omega)) (Nat.le_add_left _ _))
  have hA' : D.Moves W kilnTy V := (Can.ambient hA h3).mono (fun i => le_trans
    (Small.pow_mono_degree (S i) (show a≤d+a by omega)) (Nat.le_add_left _ _))
  exact ⟨d+a,caseM hd' (caseM hA' (hr.weaken (Dom.of_le fun i => Nat.le_add_right _ _)))⟩

end PreparedWorkingFourier
end Bench
end
end FourierSchur.OriginalSynchronizedSubstitution
