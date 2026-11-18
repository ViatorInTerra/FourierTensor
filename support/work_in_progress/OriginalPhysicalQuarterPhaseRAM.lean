import work_in_progress.OriginalPhysicalChirpRAM

/-!
Paid fourth-root phases on arbitrary complex physical data. A table of
`i^popcount(a)` is built by an actual scalar/word program, with every loop,
read, arithmetic operation and initialized table entry charged. Application
uses packed physical-row addresses, without scanning f bits per coefficient.
The program has no recursive kernel calls.
-/
namespace FourierSchur.OriginalPhysicalQuarterPhaseRAM
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty Matrix Finset
noncomputable section

def quarterBit (n : ℕ) : ℂ := if n=0 then 1 else Complex.I

def quarterPrefix (n a : ℕ) : ℂ :=
  ∏ j ∈ range n, quarterBit (a/2^j%2)

theorem quarterPrefix_succ (n a : ℕ) :
    quarterPrefix (n+1) a=quarterPrefix n a*quarterBit (a/2^n%2) := by
  simp only [quarterPrefix,prod_range_succ]

def quarterTab (f : ℕ) : Tape ℂ :=
  (bits f).tape (fun a => quarterPrefix f ((bits f).loc a))

section Preparation
universe U
variable {ι : Type U} {m : Bool} {s : Ty} {x : ι→T s} {B f : ι→ℕ}

private theorem quarterBit_read {n : ι→ℕ}
    (hn : Has m B s w x n) (hI : Has m B s sc x (fun _ => Complex.I)) :
    Has m B s sc x (fun i => quarterBit (n i)) := by
  apply Can.testz hn
  · apply (Can.one (m:=m) (B:=fun i : {i // n i=0} => B i.val)
      (s:=s) (x:=fun i => x i.val) (W:=fun _ => 0)).cong (fun _ => rfl)
    intro i
    simp [quarterBit,i.property]
  · apply (hI.reindex (fun i : {i // n i≠0} => i.val)).cong (fun _ => rfl)
    intro i
    simp [quarterBit,i.property]

private theorem quarter_value (a : ι→ℕ)
    (hf : Has m B s w x f) (ha : Has m B s w x a)
    (hI : Has m B s sc x (fun _ => Complex.I))
    (hB : Small B f) (hd : Small B fun i => 2^f i) (hs : Small B a) :
    Can m B s sc x (fun i => quarterPrefix (f i) (a i)) f := by
  let g i j := (2^j,quarterPrefix j (a i))
  let Y := p w sc
  let T₀ := p s (p w Y)
  let env (d : During f) : T T₀ := (x d.i,d.j,g d.i d.j)
  let B' (d : During f) := B d.i
  let E (d : During f) := 2^d.j
  have sE : Small B' E := (hd.reindex (During.i (n:=f))).mono
    (fun d => Nat.pow_le_pow_right (by omega) d.hj.le)
  have step : Has m B' T₀ Y env (fun d => g d.i (d.j+1)) := by
    have cg : Has m B' T₀ Y env (fun d => g d.i d.j) := Can.snd Can.second
    have ce : Has m B' T₀ w env E := cg.fst
    have c2 : Has m B' T₀ w env (fun _ => 2) := Can.wc _
    have sa : Small B' (fun d : During f => a d.i) := hs.reindex During.i
    have ca : Has m B' T₀ w env (fun d => a d.i) :=
      Can.first.then_do (ha.reindex During.i)
    have cb := (ca.dvdW ce sa).modW c2 sa.div
    have ci : Has m B' T₀ sc env (fun _ => Complex.I) :=
      Can.first.then_do (hI.reindex During.i)
    have ct := quarterBit_read cb ci
    refine ((ce.times c2 sE (Small.const ..)).pair (cg.snd.mul ct)).cong
      (fun _ => rfl) ?_
    intro d
    apply Prod.ext
    · exact (pow_succ ..).symm
    · exact (quarterPrefix_succ d.j (a d.i)).symm
  have c0 : Has m B s Y x (fun i => g i 0) := by
    simp only [g,quarterPrefix,range_zero,prod_empty,pow_zero]
    exact (Can.wc _).pair Can.one
  have hh := Can.loop (t:=Y) (v:=g) (uB:=fun _ _ => 0) hf c0 step hB
  simpa [g] using hh.snd

/-- The variable-sized scalar table is computed and written inside the
program. Its full preparation allowance is bounded by 4^f, also at f=0. -/
theorem quarter_prepare (hf : Has m B s w x f)
    (hg : Has m B s w x (fun i => 2^f i))
    (hI : Has m B s sc x (fun _ => Complex.I))
    (hB : Small B f) (hd : Small B fun i => 2^f i) :
    Can m B s (a sc) x (fun i => quarterTab (f i)) (fun i => (2^f i)^2) := by
  let I i := Bits (f i)
  let D i := bits (f i)
  let BB (d : Σ i, I i) := B d.1
  let VV (d : Σ i, I i) : T (p s w) := (x d.1,(D d.1).loc d.2)
  have hh : Can m BB (p s w) sc VV (fun d : Σ i, I i =>
      quarterPrefix (f d.1) ((bits (f d.1)).loc d.2)) (fun d => f d.1) := by
    exact quarter_value _
      (Can.first.then_do (hf.reindex Sigma.fst)) Can.second
      (Can.first.then_do (hI.reindex Sigma.fst)) (hB.reindex Sigma.fst)
      (hd.reindex Sigma.fst)
      (Small.loc (x:=fun d : Σ i, I i => d.2) (L:=fun d => bits (f d.1))
        (hd.reindex Sigma.fst))
  have ht := Can.layout (t:=sc) (P:=f) (L:=D) (α:=I)
    (v:=fun i j => quarterPrefix (f i) ((bits (f i)).loc j)) hg hh hd
  refine ht.mono (fun i => ?_)
  change 0+2^f i+2^f i*f i ≤ _
  have he : f i+1≤2^f i := Nat.lt_two_pow_self
  have H := Nat.mul_le_mul_left (2^f i) he
  simpa [pow_two,Nat.mul_add,add_comm] using H

theorem quarter_lookup {W : ι→ℕ} (v : ∀ i, Bits (f i))
    (ht : Can m B s (a sc) x (fun i => quarterTab (f i)) W)
    (ha : Can m B s w x (fun i => (bits (f i)).loc (v i)) W) :
    Can m B s sc x (fun i => quarterPrefix (f i) ((bits (f i)).loc (v i))) W :=
  Can.fetch (t:=sc) (L:=fun i => bits (f i)) (i:=v)
    (v:=fun i a => quarterPrefix (f i) ((bits (f i)).loc a)) ht ha
end Preparation

section Semantics
variable {α ρ δ : Type*} [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ] [Fintype δ]

def phaseRow (a : Option α) (f : ℕ) (q : Sky α f) : Bits f :=
  match a with
  | none => fun _ => 1
  | some a => fun j => q j a

/-- `none` supplies the global amplification phase i^f; `some a` supplies
the physical row phase i^popcount(row a). Repetition gives all four roots. -/
def quarterFactor (L : δ→Option α) (f : ℕ) (q : Sky α f) : ℂ :=
  ∏ d, quarterPrefix f ((bits f).loc (phaseRow (L d) f q))

def quarterData (l : ρ) (L : δ→Option α) (r f : ℕ)
    (v : Grain α ρ r f) : Grain α ρ r f :=
  fun q => if q.1=l then quarterFactor L f q.2.2*v q else v q

theorem quarterBit_cast (n : ℕ) (hn : n<2) : quarterBit n=tint (n:F) := by
  interval_cases n <;> norm_num [quarterBit,tint]

theorem quarterPrefix_columns (f : ℕ) (q : Bits f) :
    quarterPrefix f ((bits f).loc q)=∏ j,tint (q j) := by
  unfold quarterPrefix
  simp_rw [quarterBit_cast _ (Nat.mod_lt _ (by decide))]
  rw [← Fin.prod_univ_eq_prod_range]
  simp only [bits_div,ZMod.natCast_zmod_val]

theorem quarterFactor_columns (L : δ→Option α) (f : ℕ) (q : Sky α f) :
    quarterFactor L f q=∏ j,∏ d,tint (phaseRow (L d) f q j) := by
  simp only [quarterFactor,quarterPrefix_columns]
  rw [Finset.prod_comm]

theorem quarterData_off (l : ρ) (L : δ→Option α) (r f : ℕ)
    (v : Grain α ρ r f) (q : Beach α ρ r f) (hq : q.1≠l) :
    quarterData l L r f v q=v q := by simp [quarterData,hq]

universe U
variable {ι : Type U} {m : Bool} {B f : ι→ℕ} {s : Ty} {x : ι→T s}
  {cl : Paint} {X : Layout α} {R : Layout ρ} {r : ℕ}
  {v : ∀ i, Grain α ρ r (f i)}

theorem quarterFactor_read (h : Rig m B f s x cl X R r v)
    (ht : Has m B s (a sc) x (fun i => quarterTab (f i)))
    (L : δ→Option α) (q : ∀ i, Beach α ρ r (f i))
    (g : Knows m B s x (fun i => (fleet X R r (f i)).loc (q i))) :
    Has m B s sc x (fun i => quarterFactor L (f i) (q i).2.2) := by
  obtain ⟨_,hb⟩ := h.addrs q g
  obtain ⟨_,hp⟩ := h.gear.grid_fetch X r hb
  apply Can.prod_cconst
  intro d
  cases he : L d with
  | some a =>
    simpa only [he,phaseRow] using quarter_lookup
      (fun i => fun j => (q i).2.2 j a) ht
      (h.gear.body_get X (fun i => (q i).2.2) a hp)
  | none =>
    have hones : Knows m B s x (fun i => (bits (f i)).loc (fun _ => (1:F))) :=
      (h.gear.power.minus (Can.wc 1) h.gear.bound).cong (fun _ => rfl) (fun i => by
        change 2^f i-1=(bits (f i)).loc (fun _ => 1)
        rw [← bits_lit]
        simp)
    simpa only [he,phaseRow] using quarter_lookup (fun _ _ => (1:F)) ht hones

theorem quarterData_read (h : Rig m B f s x cl X R r v)
    (ht : Has m B s (a sc) x (fun i => quarterTab (f i)))
    (l : ρ) (L : δ→Option α) (q : ∀ i, Beach α ρ r (f i))
    (g : Knows m B s x (fun i => (fleet X R r (f i)).loc (q i))) :
    Has m B s (c cl) x (fun i => quarterData l L r (f i) (v i) (q i)) := by
  obtain ⟨hr,hb⟩ := h.addrs q g
  have hv := h.read q hr hb
  have hc := quarterFactor_read h ht L q g
  apply Can.cases_code (q:=fun i => (q i).1) R hr
  intro role
  by_cases he : role=l
  · apply ((hc.mul hv).reindex (fun i : {i // (q i).1=role} => i.val)).cong
      (fun _ => rfl)
    intro i
    simp [quarterData,i.property,he]
  · apply (hv.reindex (fun i : {i // (q i).1=role} => i.val)).cong (fun _ => rfl)
    intro i
    simp [quarterData,i.property,he]

/-- Fully charged uniform native code; every complex data coordinate is
read and written separately. Only the address-dependent phase is tabled. -/
theorem quarterData_native (h : Rig m B f s x cl X R r v) (hr : 2≤X.n)
    (l : ρ) (L : δ→Option α) :
    Can m B s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (quarterData l L r (f i) (v i)))
      (fun i => (fleet X R r (f i)).n) := by
  have hB : Small B f := h.gear.bound.mono (fun i => (Nat.lt_two_pow_self (n:=f i)).le)
  have Hprep := quarter_prepare h.gear.given h.gear.power h.imag hB h.gear.bound
  have Hwide : Can m B s (a sc) x (fun i => quarterTab (f i))
      (fun i => (fleet X R r (f i)).n) := by
    apply Hprep.mono
    intro i
    change (2^f i)^2≤R.n*(2^r*(2^f i)^X.n)
    have hp : (2^f i)^2≤(2^f i)^X.n := Nat.pow_le_pow_right (by positivity) hr
    have h₁ : (2^f i)^X.n≤2^r*(2^f i)^X.n :=
      Nat.le_mul_of_pos_left _ (by positivity)
    have hR : 0<R.n := Nat.lt_of_le_of_lt (Nat.zero_le _) (R.bd l)
    exact hp.trans (h₁.trans (Nat.le_mul_of_pos_left _ hR))
  let env i : T (p s (a sc)) := (x i,quarterTab (f i))
  have hg := h.gather id env (t:=p s (a sc)) Can.first
  have ht : Has m B (p s (a sc)) (a sc) env (fun i => quarterTab (f i)) := Can.second
  have HC : Can m B (p s (a sc)) (bundle cl) env
      (fun i => (fleet X R r (f i)).tape (quarterData l L r (f i) (v i)))
      (fun i => (fleet X R r (f i)).n) := by
    refine hg.chart _ ?_
    let S := Σ i, Beach α ρ r (f i)
    let env' (d : S) : T (p (p s (a sc)) w) :=
      (env d.1,(fleet X R r (f d.1)).loc d.2)
    have hh := hg.gather (fun d : S => d.1) env' (t:=p (p s (a sc)) w) Can.first
    have htab : Has m (fun d : S => B d.1) (p (p s (a sc)) w) (a sc) env'
        (fun d => quarterTab (f d.1)) :=
      Can.first.then_do (ht.reindex (fun d : S => d.1))
    exact quarterData_read hh htab l L (fun d => d.2) Can.second
  exact Hwide.bind HC
end Semantics
end
end FourierSchur.OriginalPhysicalQuarterPhaseRAM
