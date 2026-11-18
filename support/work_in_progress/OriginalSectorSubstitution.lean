import vendor.OpenAIUniformFourierBundle

/-! A parameterized replacement of the tensor executor used by the original
sector algorithm.  The hypothesis is an actual `Can` certificate for one
uniform closed program on every dyadic width and every input vector.  Its
integer high-water mark is retained by `Can.ambient`; no arithmetic-only
circuit guarantee is silently promoted to a RAM guarantee.

The extra `+1` in the profile charges the linear packing and routing work.
This file does not instantiate a faster tensor executor or prove a density
bound.  In the closed interface below, any coefficient preparation required
by the executor is part of its `Can` work budget. -/

namespace FourierSchur.OriginalSectorSubstitution
open OAI OAI.PowerSaving OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty OAI.PowerSaving.RAM.Bench Finset Grove Shard Binary
noncomputable section
universe U V

/-- An index includes the complete, arbitrary input vector. -/
abbrev TensorInput := Σ k : ℕ, Bits k → ℂ

/-- A single executable RAM certificate, uniform over both width and input.
The work is `2^k * t(k)` and the integer cap is polynomial in `2^k+2`. -/
def CompleteTensorExecutor (cl : Paint) (m : Bool) (t : ℕ → ℕ) : Prop :=
  Can m (fun i : TensorInput => 2^i.1) (simIn cl) (bundle cl)
    (fun i => givenBits cl i.1 i.2)
    (fun i => (bits i.1).tape (ripple i.1 i.2))
    (fun i => 2^i.1 * t i.1)

theorem CompleteTensorExecutor.run {cl : Paint} {m : Bool} {t : ℕ → ℕ}
    (h : CompleteTensorExecutor cl m t) {ι : Type U} (k : ι → ℕ)
    (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i))
      (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i * t (k i)) :=
  Can.reindex h (fun i => ⟨k i,v i⟩)

/-- Prepared scalar or table registers precede the arbitrary input tape.
For `s = sc`, this is the interface `(k,I,parentRoot,inputTape)`. -/
abbrev suppliedIn (s : Ty) (cl : Paint) := p w (p sc (p s (bundle cl)))

def suppliedBits (s : Ty) (cl : Paint) (table : ℕ → T s)
    (k : ℕ) (v : Bits k → ℂ) : T (suppliedIn s cl) :=
  (k,Complex.I,table k,(bits k).tape v)

/-- Online execution with supplied, shared preparation registers.  This is
an actual program certificate, including operation and integer bounds. -/
def SuppliedTensorExecutor (s : Ty) (table : ℕ → T s)
    (cl : Paint) (m : Bool) (t : ℕ → ℕ) : Prop :=
  Can m (fun i : TensorInput => 2^i.1) (suppliedIn s cl) (bundle cl)
    (fun i => suppliedBits s cl table i.1 i.2)
    (fun i => (bits i.1).tape (ripple i.1 i.2))
    (fun i => 2^i.1 * t i.1)

theorem SuppliedTensorExecutor.run {s : Ty} {table : ℕ → T s}
    {cl : Paint} {m : Bool} {t : ℕ → ℕ}
    (h : SuppliedTensorExecutor s table cl m t) {ι : Type U} (k : ι → ℕ)
    (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (suppliedIn s cl) (bundle cl)
      (fun i => suppliedBits s cl table (k i) (v i))
      (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i * t (k i)) :=
  Can.reindex h (fun i => ⟨k i,v i⟩)

/-- All requested prepared registers are obtained from the shared environment
by one constant-work program.  Their construction is a separate hypothesis;
this certificate does not supply any preparation theorem. -/
def TableReader {m : Bool} {ι : Type U} (b : OAI.PowerSaving.RAM.Bench m ι)
    (l : ι → ℕ) (s : Ty) (table : ℕ → T s) : Prop :=
  Can m (fun d : Σ i, Fin (l i+1) => b.size d.1) (p b.tray w) s
    (fun d => (b.env d.1,d.2.val)) (fun d => table d.2.val) (fun _ => 0)

theorem TableReader.readAt {m : Bool} {ι : Type U}
    {b : OAI.PowerSaving.RAM.Bench m ι} {l k : ι → ℕ}
    {s : Ty} {table : ℕ → T s} (h : TableReader b l s table)
    (hk : b.Nick k) (hg : ∀ i, k i ≤ l i) :
    b.Moves (fun _ => 0) s (fun i => table (k i)) := by
  have hi := Can.reindex h (fun i =>
    (⟨i,⟨k i,Nat.lt_succ_of_le (hg i)⟩⟩ : Σ i, Fin (l i+1)))
  exact Can.then_do ((envNow b).pair hk.close) hi

theorem TableReader.transfer {m : Bool} {ι : Type U} {κ : Type V}
    {b : OAI.PowerSaving.RAM.Bench m ι} {q : OAI.PowerSaving.RAM.Bench m κ}
    {l : κ → ℕ} {s : Ty} {table : ℕ → T s}
    (h : TableReader q l s table) {f : ι → κ} (g : b.Instant q f) :
    TableReader b (fun i => l (f i)) s table := by
  let J := Σ i : ι, Fin (l (f i)+1)
  have hp : Can m (fun j : J => b.size j.1) (p b.tray w) q.tray
      (fun j => (b.env j.1,j.2.val)) (fun j => q.env (f j.1)) (fun _ => 0) :=
    Can.then_do Can.first (Can.reindex g.prep (fun j : J => j.1))
  have hr := Can.reindex h (fun j : J =>
    (⟨f j.1,j.2⟩ : Σ i : κ, Fin (l i+1)))
  exact Can.then_do (Can.pair hp Can.second)
    (hr.ambient (g.covers.reindex (fun j : J => j.1)))

namespace Bench
variable {m : Bool} {ι : Type U} {b : OAI.PowerSaving.RAM.Bench m ι}
  {cl : Paint} {k l n : ι → ℕ} {x : ι → Line} {f : ι → ℕ → Shard}
  {t : ℕ → ℕ} {s : Ty} {table : ℕ → T s}

/-- The original `Bench.gleamT` with an executable tensor certificate supplied
by the caller.  `t(l)+1` includes tape construction and routing. -/
theorem gleamT_executor (hExec : CompleteTensorExecutor cl m t)
    (ht : Monotone t) (hw : ∀ i, n i = 2^k i) (hg : ∀ i, k i ≤ l i)
    (hn : b.Nick n) (hk : b.Nick k)
    (hI : b.Moves (fun _ => 0) sc fun _ => Complex.I)
    (hx : b.Moves n (a (c cl)) fun i => Tape.tab (n i) (x i)) :
    b.Moves (fun i => n i * (t (l i)+1)) (a (c cl)) fun i =>
      Tape.tab (n i) (gleam (k i) (x i)) := by
  let W i := n i * (t (l i)+1)
  let v i (d : Bits (k i)) := x i ((bits (k i)).loc d)
  have hroute : Dom W n := Dom.of_le (fun i =>
    Nat.le_mul_of_pos_right _ (Nat.succ_pos (t (l i))))
  have hx' : b.Moves W (a (c cl)) fun i => (bits (k i)).tape (v i) := by
    refine (hx.weaken hroute).congr ?_
    intro i
    refine Layout.verify _ _ 0 (v i) (hw i) ?_
    intro d
    rw [Tape.look_tab, hw,
      if_pos (show (bits (k i)).loc d < 2^k i from (bits _).bd d)]
  have hi := hExec.run k v
  have he : b.Moves W (a (c cl)) fun i =>
      (bits (k i)).tape (ripple (k i) (v i)) := by
    have hu : Small b.size (fun i => 2^k i) := hn.small.mono fun i => (hw i).ge
    have hj : ∀ i, 2^k i * t (k i) ≤ W i := fun i =>
      Nat.mul_le_mul (by rw [hw])
        ((ht (hg i)).trans (Nat.le_succ _))
    exact Can.then_do ((hk.close.ease W).pair ((hI.ease W).pair hx'))
      ((hi.ambient hu).mono hj)
  refine he.congr ?_
  intro i
  symm
  apply Layout.verify _ _ 0 (ripple (k i) (v i)) (hw i)
  intro d
  rw [Tape.look_tab, hw,
    if_pos (show (bits (k i)).loc d < 2^k i from (bits _).bd d)]
  exact gleam_loc _ _ d

/-- Executor substitution with materialized shared table registers. -/
theorem gleamT_supplied_executor (hExec : SuppliedTensorExecutor s table cl m t)
    (ht : Monotone t) (hw : ∀ i, n i = 2^k i) (hg : ∀ i, k i ≤ l i)
    (hn : b.Nick n) (hk : b.Nick k)
    (hI : b.Moves (fun _ => 0) sc fun _ => Complex.I)
    (hTable : b.Moves (fun _ => 0) s fun i => table (k i))
    (hx : b.Moves n (a (c cl)) fun i => Tape.tab (n i) (x i)) :
    b.Moves (fun i => n i * (t (l i)+1)) (a (c cl)) fun i =>
      Tape.tab (n i) (gleam (k i) (x i)) := by
  let W i := n i * (t (l i)+1)
  let v i (d : Bits (k i)) := x i ((bits (k i)).loc d)
  have hroute : Dom W n := Dom.of_le (fun i =>
    Nat.le_mul_of_pos_right _ (Nat.succ_pos (t (l i))))
  have hx' : b.Moves W (a (c cl)) fun i => (bits (k i)).tape (v i) := by
    refine (hx.weaken hroute).congr ?_
    intro i
    refine Layout.verify _ _ 0 (v i) (hw i) ?_
    intro d
    rw [Tape.look_tab, hw,
      if_pos (show (bits (k i)).loc d < 2^k i from (bits _).bd d)]
  have hi := hExec.run k v
  have he : b.Moves W (a (c cl)) fun i =>
      (bits (k i)).tape (ripple (k i) (v i)) := by
    have hu : Small b.size (fun i => 2^k i) := hn.small.mono fun i => (hw i).ge
    have hj : ∀ i, 2^k i * t (k i) ≤ W i := fun i =>
      Nat.mul_le_mul (by rw [hw])
        ((ht (hg i)).trans (Nat.le_succ _))
    exact Can.then_do ((hk.close.ease W).pair ((hI.ease W).pair ((hTable.ease W).pair hx')))
      ((hi.ambient hu).mono hj)
  refine he.congr ?_
  intro i
  symm
  apply Layout.verify _ _ 0 (ripple (k i) (v i)) (hw i)
  intro d
  rw [Tape.look_tab, hw,
    if_pos (show (bits (k i)).loc d < 2^k i from (bits _).bd d)]
  exact gleam_loc _ _ d

namespace Weft
variable {j : ι → ℕ}

-- rolls at a sector start.
lemma shine_executor (hExec : CompleteTensorExecutor cl m t) (hmono : Monotone t) (h : b.Weft cl n l f x) (hj : b.Nick j) (hg : ∀ i,j i<n i)
    (hz : ∀ i,(patch (n i) (f i) (j i)).seat=0) :
    b.Moves (fun i => seatfare (n i) (f i) (j i) * (t (l i)+1)) (a (c cl))
      fun i => rolls (n i) (f i) (x i) (j i) := by
  let B i := patch (n i) (f i) (j i)
  let Q i := (B i).width
  have HK := h.kitOf hj hg
  have he (i : ι) : (B i).Mark (n i) (l i) := (h.mat.shape i).patch_mark (hg i)
  have hh (i : ι) : j i+Q i ≤ n i := by
    have A : (B i).tip ≤ n i := (he i).endsBy
    have hx : (B i).addr=j i := (h.mat.shape i).patch_addr (hg i)
    have hy : (B i).seat=0 := hz i
    unfold tip at A; unfold addr at hx; dsimp only [Q]; omega
  let S i := slit (n i) (f i) (x i) (j i)
  have ht : b.Moves Q (a (c cl)) fun i => Tape.tab (Q i) (S i) := by
    have F := Instant.scan b Q
    have hi := chop HK.widths
    have hw := (hj.transfer F).add hi
    exact arrayNow HK.widths (t:=c cl) S ((h.transfer F).stowOf hw fun i =>
      lt_of_lt_of_le (Nat.add_lt_add_left i.hj _) (hh _))
  simp only [seatfare,rolls,hz,ite_true]
  exact gleamT_executor hExec hmono (fun i => (he i).size) (fun i => (he i).tall)
    HK.widths HK.tall h.unitI ht

lemma arrays_executor (hExec : CompleteTensorExecutor cl m t) (hmono : Monotone t) (h : b.Weft cl n l f x) :
    b.Moves (fun i => n i*(t (l i)+1)) (a (a (c cl)))
      fun i => Tape.tab (n i) (rolls (n i) (f i) (x i)) := by
  let W (i : ι) := n i*(t (l i)+1)
  let D := b.scan n
  let C (i : ι) j := seatfare (n i) (f i) j*(t (l i)+1)
  let Y (i : ι) := rolls (n i) (f i) (x i)
  have hn := h.mat.length
  have F := Instant.scan b n
  have hk := h.transfer F
  have hs := chop hn
  have hb := (hk.kitOf hs During.hj).seat
  have ht : D.Moves (fun d => C d.i d.j) (a (c cl)) fun d => Y d.i d.j := by
    let Q (i : During n) := (patch (n i.i) (f i.i) i.j).seat
    refine inspectz (n:=Q) hb ?_ ?_
    · have ha := Instant.along D (Subtype.val (p:=fun i => Q i=0))
      exact shine_executor hExec hmono (hk.transfer ha) (hs.transfer ha) (fun i => i.val.hj)
        (fun i => i.property)
    · let A := {i // Q i ≠ 0}
      let M := D.along (Subtype.val (p:=fun i => Q i≠0))
      have hh := arrayNow (b:=M) (t:=c cl) (Nick.wc 0) (fun _ _ => 0) Moves.zero
      refine (hh.weaken (Dom.const _ _)).congr ?_
      intro i
      have hB : Q i.val ≠ 0 := i.property
      simp only [Q] at hB
      simp only [Y,rolls,hB,↓reduceIte]
  have he := arrayM (t:=a (c cl)) hn Y ht (u:=C)
  refine he.weaken ?_
  refine ⟨3,fun i => ?_⟩
  dsimp only [C]
  rw [← sum_mul, fare_sum _ _ _ (h.mat.shape i)]
  have hm : n i ≤ n i*(t (l i)+1) :=
    Nat.le_mul_of_pos_right (n i) (Nat.succ_pos (t (l i)))
  omega

lemma woven_executor (hExec : CompleteTensorExecutor cl m t) (hmono : Monotone t) (h : b.Weft cl n l f x) :
    b.Moves (fun i => n i*(t (l i)+1)) (a (c cl))
      fun i => Tape.tab (n i) fun j =>
        glimpse (n i) (f i) (x i) (f i j).start (f i j).seat := by
  let W i := n i*(t (l i)+1)
  let T i := rolls (n i) (f i) (x i)
  let V i := Tape.tab (n i) (T i)
  let D := b.extend (a (a (c cl))) V
  have F := Instant.extend b (t:=a (a (c cl))) V
  have G := Instant.scan D n
  have HK : Dom W n := Dom.of_le (fun i => Nat.le_mul_of_pos_right _ (Nat.succ_pos (t (l i))))
  let B (d : During n) := f d.i d.j
  have hn := (h.mat.length.transfer F)
  have hh := (h.mat.transfer (G.next F)).kitOf (chop hn) During.hj
  have hg (d : During n) := (h.mat.shape d.i).mark d.j d.hj
  have hm (d : During n) : (B d).start < n d.i := (hg d).starts.trans_le (hg d).endsBy
  have ht := Moves.pick (t:=a (c cl)) (n:=fun d : During n => n d.i) (fun d j => T d.i j)
    ((cherry (W:=fun _ => 0) b (t:=a (a (c cl))) V).transfer G)
    hh.starts.close hm
  have he (d : During n) :
      T d.i (B d).start = Tape.tab (B d).width
        (glimpse (n d.i) (f d.i) (x d.i) (B d).start) := by
    have hM := (h.mat.shape d.i).patch_align d.hj (le_refl (B d).start) (hg d).starts
    have he : (patch (n d.i) (f d.i) (B d).start).seat=0 := hM.2.trans (Nat.sub_self _)
    simp only [T,rolls,he,ite_true]
    rw [hM.1.2.1]
  have hj := Moves.pick (b:=D.scan n) (n:=fun d => (B d).width) (t:=c cl)
    (fun d => glimpse (n d.i) (f d.i) (x d.i) (B d).start) (ht.congr he) hh.seat.close
    (fun d => (hg d).place)
  exact caseM (arrays_executor hExec hmono h) ((arrayNow (t:=c cl) hn (fun i j => glimpse (n i) (f i) (x i) (f i j).start (f i j).seat) hj).weaken HK)

end Weft

lemma Matting.cardT_executor (hExec : CompleteTensorExecutor cl m t) (hmono : Monotone t) (h : b.Matting n l f)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (n i) (x i))
    (hI : b.Moves (fun _ => 0) sc fun _ => Complex.I) :
    b.Moves (fun i => n i*(t (l i)+1)) (a (c cl))
      fun i => Tape.tab (n i) fun j =>
        glimpse (n i) (f i) (x i) (f i j).start (f i j).seat := by
  let V i := Tape.tab (n i) (rag (n i) (f i) (x i))
  let D := b.extend (a (ragTy cl)) V
  have F := Instant.extend b (t:=a (ragTy cl)) V
  have hk : D.Weft cl n l f x := ⟨h.transfer F,cherry (t:=a (ragTy cl)) b V,hI.transfer F⟩
  refine caseM ((h.packT hx).weaken (Dom.of_le (fun i =>
    Nat.le_mul_of_pos_right _ (Nat.succ_pos (t (l i)))))) (Weft.woven_executor hExec hmono hk)

/- Supplied-table sector pipeline; each table lookup is charged by `TableReader`. -/
namespace Weft
variable {j : ι → ℕ}

-- rolls at a sector start.
lemma shine_supplied_executor (hExec : SuppliedTensorExecutor s table cl m t) (hmono : Monotone t) (hRead : TableReader b l s table) (h : b.Weft cl n l f x) (hj : b.Nick j) (hg : ∀ i,j i<n i)
    (hz : ∀ i,(patch (n i) (f i) (j i)).seat=0) :
    b.Moves (fun i => seatfare (n i) (f i) (j i) * (t (l i)+1)) (a (c cl))
      fun i => rolls (n i) (f i) (x i) (j i) := by
  let B i := patch (n i) (f i) (j i)
  let Q i := (B i).width
  have HK := h.kitOf hj hg
  have he (i : ι) : (B i).Mark (n i) (l i) := (h.mat.shape i).patch_mark (hg i)
  have hh (i : ι) : j i+Q i ≤ n i := by
    have A : (B i).tip ≤ n i := (he i).endsBy
    have hx : (B i).addr=j i := (h.mat.shape i).patch_addr (hg i)
    have hy : (B i).seat=0 := hz i
    unfold tip at A; unfold addr at hx; dsimp only [Q]; omega
  let S i := slit (n i) (f i) (x i) (j i)
  have ht : b.Moves Q (a (c cl)) fun i => Tape.tab (Q i) (S i) := by
    have F := Instant.scan b Q
    have hi := chop HK.widths
    have hw := (hj.transfer F).add hi
    exact arrayNow HK.widths (t:=c cl) S ((h.transfer F).stowOf hw fun i =>
      lt_of_lt_of_le (Nat.add_lt_add_left i.hj _) (hh _))
  simp only [seatfare,rolls,hz,ite_true]
  exact gleamT_supplied_executor hExec hmono (fun i => (he i).size) (fun i => (he i).tall)
    HK.widths HK.tall h.unitI (hRead.readAt HK.tall fun i => (he i).tall) ht

lemma arrays_supplied_executor (hExec : SuppliedTensorExecutor s table cl m t) (hmono : Monotone t) (hRead : TableReader b l s table) (h : b.Weft cl n l f x) :
    b.Moves (fun i => n i*(t (l i)+1)) (a (a (c cl)))
      fun i => Tape.tab (n i) (rolls (n i) (f i) (x i)) := by
  let W (i : ι) := n i*(t (l i)+1)
  let D := b.scan n
  let C (i : ι) j := seatfare (n i) (f i) j*(t (l i)+1)
  let Y (i : ι) := rolls (n i) (f i) (x i)
  have hn := h.mat.length
  have F := Instant.scan b n
  have hk := h.transfer F
  have hs := chop hn
  have hb := (hk.kitOf hs During.hj).seat
  have ht : D.Moves (fun d => C d.i d.j) (a (c cl)) fun d => Y d.i d.j := by
    let Q (i : During n) := (patch (n i.i) (f i.i) i.j).seat
    refine inspectz (n:=Q) hb ?_ ?_
    · have ha := Instant.along D (Subtype.val (p:=fun i => Q i=0))
      exact shine_supplied_executor hExec hmono ((hRead.transfer F).transfer ha) (hk.transfer ha) (hs.transfer ha) (fun i => i.val.hj)
        (fun i => i.property)
    · let A := {i // Q i ≠ 0}
      let M := D.along (Subtype.val (p:=fun i => Q i≠0))
      have hh := arrayNow (b:=M) (t:=c cl) (Nick.wc 0) (fun _ _ => 0) Moves.zero
      refine (hh.weaken (Dom.const _ _)).congr ?_
      intro i
      have hB : Q i.val ≠ 0 := i.property
      simp only [Q] at hB
      simp only [Y,rolls,hB,↓reduceIte]
  have he := arrayM (t:=a (c cl)) hn Y ht (u:=C)
  refine he.weaken ?_
  refine ⟨3,fun i => ?_⟩
  dsimp only [C]
  rw [← sum_mul, fare_sum _ _ _ (h.mat.shape i)]
  have hm : n i ≤ n i*(t (l i)+1) :=
    Nat.le_mul_of_pos_right (n i) (Nat.succ_pos (t (l i)))
  omega

lemma woven_supplied_executor (hExec : SuppliedTensorExecutor s table cl m t) (hmono : Monotone t) (hRead : TableReader b l s table) (h : b.Weft cl n l f x) :
    b.Moves (fun i => n i*(t (l i)+1)) (a (c cl))
      fun i => Tape.tab (n i) fun j =>
        glimpse (n i) (f i) (x i) (f i j).start (f i j).seat := by
  let W i := n i*(t (l i)+1)
  let T i := rolls (n i) (f i) (x i)
  let V i := Tape.tab (n i) (T i)
  let D := b.extend (a (a (c cl))) V
  have F := Instant.extend b (t:=a (a (c cl))) V
  have G := Instant.scan D n
  have HK : Dom W n := Dom.of_le (fun i => Nat.le_mul_of_pos_right _ (Nat.succ_pos (t (l i))))
  let B (d : During n) := f d.i d.j
  have hn := (h.mat.length.transfer F)
  have hh := (h.mat.transfer (G.next F)).kitOf (chop hn) During.hj
  have hg (d : During n) := (h.mat.shape d.i).mark d.j d.hj
  have hm (d : During n) : (B d).start < n d.i := (hg d).starts.trans_le (hg d).endsBy
  have ht := Moves.pick (t:=a (c cl)) (n:=fun d : During n => n d.i) (fun d j => T d.i j)
    ((cherry (W:=fun _ => 0) b (t:=a (a (c cl))) V).transfer G)
    hh.starts.close hm
  have he (d : During n) :
      T d.i (B d).start = Tape.tab (B d).width
        (glimpse (n d.i) (f d.i) (x d.i) (B d).start) := by
    have hM := (h.mat.shape d.i).patch_align d.hj (le_refl (B d).start) (hg d).starts
    have he : (patch (n d.i) (f d.i) (B d).start).seat=0 := hM.2.trans (Nat.sub_self _)
    simp only [T,rolls,he,ite_true]
    rw [hM.1.2.1]
  have hj := Moves.pick (b:=D.scan n) (n:=fun d => (B d).width) (t:=c cl)
    (fun d => glimpse (n d.i) (f d.i) (x d.i) (B d).start) (ht.congr he) hh.seat.close
    (fun d => (hg d).place)
  exact caseM (arrays_supplied_executor hExec hmono hRead h) ((arrayNow (t:=c cl) hn (fun i j => glimpse (n i) (f i) (x i) (f i j).start (f i j).seat) hj).weaken HK)

end Weft

lemma Matting.cardT_supplied_executor (hExec : SuppliedTensorExecutor s table cl m t) (hmono : Monotone t) (hRead : TableReader b l s table) (h : b.Matting n l f)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (n i) (x i))
    (hI : b.Moves (fun _ => 0) sc fun _ => Complex.I) :
    b.Moves (fun i => n i*(t (l i)+1)) (a (c cl))
      fun i => Tape.tab (n i) fun j =>
        glimpse (n i) (f i) (x i) (f i j).start (f i j).seat := by
  let V i := Tape.tab (n i) (rag (n i) (f i) (x i))
  let D := b.extend (a (ragTy cl)) V
  have F := Instant.extend b (t:=a (ragTy cl)) V
  have hk : D.Weft cl n l f x := ⟨h.transfer F,cherry (t:=a (ragTy cl)) b V,hI.transfer F⟩
  refine caseM ((h.packT hx).weaken (Dom.of_le (fun i =>
    Nat.le_mul_of_pos_right _ (Nat.succ_pos (t (l i)))))) (Weft.woven_supplied_executor hExec hmono (hRead.transfer F) hk)

end Bench
end
end FourierSchur.OriginalSectorSubstitution
