import work_in_progress.OriginalGroupedWordRAM

/-!
Paid physical-coordinate sign chirps. The small dot-parity table is prepared
by an actual word program. Its O(f*4^f) work fits the existing full bank
allowance when the physical layout has at least three coordinates. Thus a
chirp does not hide a scan of all f columns for every input coefficient.
Only fixed rational signs multiply arbitrary complex data.
-/
namespace FourierSchur.OriginalPhysicalChirpRAM
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty Matrix Finset
noncomputable section

def dotParity (n a b : ℕ) : ℕ :=
  (∑ j ∈ range n, (a/2^j%2)*(b/2^j%2))%2

theorem dotParity_lt (n a b : ℕ) : dotParity n a b<2 :=
  Nat.mod_lt _ (by decide)

theorem dotParity_succ (n a b : ℕ) :
    dotParity (n+1) a b=(dotParity n a b+(a/2^n%2)*(b/2^n%2))%2 := by
  simp only [dotParity,sum_range_succ,Nat.add_mod,Nat.mod_mod]

def dotTab (f : ℕ) : Tape ℕ :=
  (xorOrd f).tape (fun v => dotParity f ((bits f).loc v.1) ((bits f).loc v.2))

section Preparation
universe U
variable {ι : Type U} {m : Bool} {s : Ty} {x : ι→T s} {B f : ι→ℕ}

private theorem dot_value (v : ∀ i, Bits (f i) × Bits (f i))
    (hf : Can m B s w x f (fun _ => 0))
    (ha : Can m B s w x (fun i => (bits (f i)).loc (v i).1) (fun _ => 0))
    (hb : Can m B s w x (fun i => (bits (f i)).loc (v i).2) (fun _ => 0))
    (hB : Small B f) (hd : Small B fun i => 2^f i) :
    Can m B s w x (fun i => dotParity (f i) ((bits (f i)).loc (v i).1)
      ((bits (f i)).loc (v i).2)) f := by
  let a1 i := (bits (f i)).loc (v i).1
  let a2 i := (bits (f i)).loc (v i).2
  let g i j := (2^j,dotParity j (a1 i) (a2 i))
  let Y := p w w
  let T₀ := p s (p w Y)
  let env (d : During f) : T T₀ := (x d.i,d.j,g d.i d.j)
  let B' (d : During f) := B d.i
  let E (d : During f) := 2^d.j
  have hv (z : ∀ i, Bits (f i)) : Small B fun i => (bits (f i)).loc (z i) :=
    Small.loc (x:=z) (L:=fun i => bits (f i)) hd
  have sE : Small B' E :=
    (hd.reindex (During.i (n:=f))).mono (fun d => Nat.pow_le_pow_right (by omega) d.hj.le)
  have sr : Small B' (fun d : During f => (g d.i d.j).2) :=
    (Small.const B' 2).mono (fun d => (dotParity_lt _ _ _).le)
  have step : Can m B' T₀ Y env (fun d => g d.i (d.j+1)) (fun _ => 0) := by
    have cg : Can m B' T₀ Y env (fun d => g d.i d.j) (fun _ => 0) := Can.snd Can.second
    have ce : Can m B' T₀ w env E (fun _ => 0) := cg.fst
    have cs2 : Can m B' T₀ w env (fun _ => 2) (fun _ => 0) := Can.wc _
    have sa : Small B' fun d : During f => a1 d.i := (hv (fun i => (v i).1)).reindex During.i
    have sb : Small B' fun d : During f => a2 d.i := (hv (fun i => (v i).2)).reindex During.i
    have ca : Can m B' T₀ w env (fun d => a1 d.i) (fun _ => 0) :=
      Can.first.then_do (ha.reindex During.i)
    have cb : Can m B' T₀ w env (fun d => a2 d.i) (fun _ => 0) :=
      Can.first.then_do (hb.reindex During.i)
    have cbit1 := (ca.dvdW ce sa).modW cs2 sa.div
    have cbit2 := (cb.dvdW ce sb).modW cs2 sb.div
    have sab : Small B' (fun d => a1 d.i/E d%2) := (sa.div (Q:=E)).mod
    have sbb : Small B' (fun d => a2 d.i/E d%2) := (sb.div (Q:=E)).mod
    have cp := cbit1.times cbit2 sab sbb
    have sp := sab.mul sbb
    have csum := cg.snd.plus cp sr sp
    have cq := csum.modW cs2 (sr.add sp)
    refine ((ce.times cs2 sE (Small.const ..)).pair cq).cong (fun _ => rfl) ?_
    intro d
    apply Prod.ext
    · exact (pow_succ ..).symm
    · exact (dotParity_succ d.j (a1 d.i) (a2 d.i)).symm
  have c0 : Can m B s Y x (fun i => g i 0) (fun _ => 0) := by
    simp only [g,dotParity,range_zero,sum_empty,Nat.zero_mod,pow_zero]
    exact (Can.wc _).pair (Can.wc _)
  have hh := Can.loop (t:=Y) (v:=g) (uB:=fun _ _ => 0) hf c0 step hB
  simpa [g,a1,a2] using hh.snd

/-- Table initialization, every word step, every write and every loop is
paid. The allowance is at most 8^f, including f=0. -/
theorem dot_prepare (hf : Can m B s w x f (fun _ => 0))
    (hg : Can m B s w x (fun i => 2^f i) (fun _ => 0))
    (hB : Small B f) (hd : Small B fun i => 2^f i) :
    Can m B s (a w) x (fun i => dotTab (f i)) (fun i => (2^f i)^3) := by
  let V i := (bits (f i)).n
  let D i := xorOrd (f i)
  have sn : Small B fun i => (D i).n := hd.mul hd
  have hn : Can m B s w x (fun i => (D i).n) (fun _ => 0) := hg.times hg hd hd
  let I i := Bits (f i) × Bits (f i)
  let BB (d : Σ i, I i) := B d.1
  let VV (d : Σ i, I i) : T (p s w) := (x d.1,(D d.1).loc d.2)
  have hh : Can m BB (p s w) w VV (fun d : Σ i, I i =>
      dotParity (f d.1) ((bits (f d.1)).loc d.2.1) ((bits (f d.1)).loc d.2.2))
      (fun d => f d.1) := by
    have hp : Can m BB (p s w) w VV (fun d => V d.1) (fun _ => 0) :=
      Can.first.then_do (hg.reindex (Sigma.fst (β:=I)))
    have hBB := sn.reindex (Sigma.fst (β:=I))
    let X (d : Σ i, I i) := bits (f d.1)
    apply dot_value (f:=fun d : Σ i, I i => f d.1) _
      (Can.first.then_do (hf.reindex (Sigma.fst (β:=I)))) _ _
      (hB.reindex Sigma.fst) (hd.reindex Sigma.fst)
    · exact Can.addr_high (u:=fun d : Σ i, I i => d.2) (L:=X) (R:=X)
        Can.second hp hBB
    · exact Can.addr_low (u:=fun d : Σ i, I i => d.2) (L:=X) (R:=X)
        Can.second hp hBB
  have ht := Can.layout (t:=w) (P:=f) (L:=D) (α:=I)
    (v:=fun i j => dotParity (f i) ((bits (f i)).loc j.1) ((bits (f i)).loc j.2)) hn hh sn
  refine ht.mono (fun i => ?_)
  change 0+2^f i*2^f i+(2^f i*2^f i)*f i ≤ _
  have he : f i<2^f i := Nat.lt_two_pow_self
  have h := Nat.mul_le_mul_left (2^f i*2^f i) he
  simpa [pow_succ,Nat.mul_add,add_comm] using h

theorem dot_lookup {W : ι→ℕ} (v : ∀ i, Bits (f i) × Bits (f i))
    (ht : Can m B s (a w) x (fun i => dotTab (f i)) W)
    (ha : Can m B s w x (fun i => (bits (f i)).loc (v i).1) W)
    (hb : Can m B s w x (fun i => (bits (f i)).loc (v i).2) W)
    (hn : Can m B s w x (fun i => 2^f i) W)
    (hd : Small B fun i => 2^f i) :
    Can m B s w x (fun i => dotParity (f i) ((bits (f i)).loc (v i).1)
      ((bits (f i)).loc (v i).2)) W :=
  Can.fetch (t:=w) (L:=fun i => xorOrd (f i)) (i:=v)
    (v:=fun i j => dotParity (f i) ((bits (f i)).loc j.1) ((bits (f i)).loc j.2)) ht
    (Can.addr_join (u:=v) (L:=fun i => bits (f i)) (R:=fun i => bits (f i))
      ha hb hn hd hd)
end Preparation

def paritySign (n : ℕ) : ℂ := if n=0 then 1 else -1

section Action
universe U
variable {α ρ δ : Type*} [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ] [Fintype δ]

/-- Each edge contributes a dot parity of two physical rows. A diagonal
edge is a linear sign, and distinct endpoints give a quadratic chirp. -/
def chirpFactor (E : δ → α × α) (f : ℕ) (q : Sky α f) : ℂ :=
  ∏ d, paritySign (dotParity f
    ((bits f).loc (fun j => q j (E d).1))
    ((bits f).loc (fun j => q j (E d).2)))

def chirpData (l : ρ) (E : δ → α × α) (r f : ℕ)
    (v : Grain α ρ r f) : Grain α ρ r f :=
  fun q => if q.1=l then chirpFactor E f q.2.2 * v q else v q

theorem paritySign_sq (n : ℕ) : paritySign n*paritySign n=1 := by
  unfold paritySign
  split <;> norm_num

theorem chirpFactor_sq (E : δ → α × α) (f : ℕ) (q : Sky α f) :
    chirpFactor E f q*chirpFactor E f q=1 := by
  rw [chirpFactor,← Finset.prod_mul_distrib]
  simp only [paritySign_sq,prod_const_one]

/-- No coordinate is discarded: the same paid chirp is its inverse. -/
theorem chirpData_involutive (l : ρ) (E : δ → α × α) (r f : ℕ)
    (v : Grain α ρ r f) : chirpData l E r f (chirpData l E r f v)=v := by
  funext q
  by_cases h : q.1=l
  · simp only [chirpData,h,ite_true,← mul_assoc,chirpFactor_sq,one_mul]
  · simp only [chirpData,h,ite_false]

variable {ι : Type U} {m : Bool} {B f : ι→ℕ} {s : Ty} {x : ι→T s}
  {cl : Paint} {X : Layout α} {R : Layout ρ} {r : ℕ}
  {v : ∀ i, Grain α ρ r (f i)}

private theorem sign_read {n : ι→ℕ} (h : Has m B s w x n) :
    Has m B s sc x (fun i => paritySign (n i)) := by
  apply Can.testz h
  · apply (Can.one (m:=m) (B:=fun i : {i // n i=0} => B i.val)
      (s:=s) (x:=fun i => x i.val) (W:=fun _ => 0)).cong (fun _ => rfl)
    intro i
    simp [paritySign,i.property]
  · apply (Can.one (m:=m) (B:=fun i : {i // n i≠0} => B i.val)
      (s:=s) (x:=fun i => x i.val) (W:=fun _ => 0)).neg.cong (fun _ => rfl)
    intro i
    simp [paritySign,i.property]

theorem chirpFactor_read (h : Rig m B f s x cl X R r v)
    (ht : Has m B s (a w) x (fun i => dotTab (f i)))
    (E : δ → α × α) (q : ∀ i, Beach α ρ r (f i))
    (g : Knows m B s x (fun i => (fleet X R r (f i)).loc (q i))) :
    Has m B s sc x (fun i => chirpFactor E (f i) (q i).2.2) := by
  obtain ⟨_,hb⟩ := h.addrs q g
  obtain ⟨_,hp⟩ := h.gear.grid_fetch X r hb
  apply Can.prod_cconst
  intro d
  have ha := h.gear.body_get X (fun i => (q i).2.2) (E d).1 hp
  have hc := h.gear.body_get X (fun i => (q i).2.2) (E d).2 hp
  exact sign_read (dot_lookup
    (fun i => ((fun j => (q i).2.2 j (E d).1),fun j => (q i).2.2 j (E d).2))
    ht ha hc h.gear.power h.gear.bound)

theorem chirpData_read (h : Rig m B f s x cl X R r v)
    (ht : Has m B s (a w) x (fun i => dotTab (f i)))
    (l : ρ) (E : δ → α × α) (q : ∀ i, Beach α ρ r (f i))
    (g : Knows m B s x (fun i => (fleet X R r (f i)).loc (q i))) :
    Has m B s (c cl) x (fun i => chirpData l E r (f i) (v i) (q i)) := by
  obtain ⟨hr,hb⟩ := h.addrs q g
  have hv := h.read q hr hb
  have hc := chirpFactor_read h ht E q g
  apply Can.cases_code (q:=fun i => (q i).1) R hr
  intro role
  by_cases hrole : role=l
  · have H := (hc.mul hv).reindex (fun i : {i // (q i).1=role} => i.val)
    apply H.cong (fun _ => rfl)
    intro i
    simp [chirpData,i.property,hrole]
  · have H := hv.reindex (fun i : {i // (q i).1=role} => i.val)
    apply H.cong (fun _ => rfl)
    intro i
    simp [chirpData,i.property,hrole]

/-- Actual uniform native code. The lookup table is built inside this
program, all output addresses are written, and arbitrary complex values
are only multiplied by prepared rational signs. No kernel callback occurs. -/
theorem chirpData_native (h : Rig m B f s x cl X R r v) (hr : 3≤X.n)
    (l : ρ) (E : δ → α × α) :
    Can m B s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (chirpData l E r (f i) (v i)))
      (fun i => (fleet X R r (f i)).n) := by
  have hB : Small B f := h.gear.bound.mono (fun i => (Nat.lt_two_pow_self (n:=f i)).le)
  have Hprep := dot_prepare h.gear.given h.gear.power hB h.gear.bound
  have Hwide : Can m B s (a w) x (fun i => dotTab (f i))
      (fun i => (fleet X R r (f i)).n) := by
    apply Hprep.mono
    intro i
    change (2^f i)^3 ≤ R.n*(2^r*(2^f i)^X.n)
    have hp : (2^f i)^3 ≤ (2^f i)^X.n := Nat.pow_le_pow_right (by positivity) hr
    have h₁ : (2^f i)^X.n ≤ 2^r*(2^f i)^X.n :=
      Nat.le_mul_of_pos_left _ (by positivity)
    have hR : 0<R.n := Nat.lt_of_le_of_lt (Nat.zero_le _) (R.bd l)
    exact hp.trans (h₁.trans (Nat.le_mul_of_pos_left _ hR))
  let env i : T (p s (a w)) := (x i,dotTab (f i))
  have hg := h.gather id env (t:=p s (a w)) Can.first
  have ht : Has m B (p s (a w)) (a w) env (fun i => dotTab (f i)) := Can.second
  have HC : Can m B (p s (a w)) (bundle cl) env
      (fun i => (fleet X R r (f i)).tape (chirpData l E r (f i) (v i)))
      (fun i => (fleet X R r (f i)).n) := by
    refine hg.chart _ ?_
    let S := Σ i, Beach α ρ r (f i)
    let env' (d : S) : T (p (p s (a w)) w) :=
      (env d.1,(fleet X R r (f d.1)).loc d.2)
    have hh := hg.gather (fun d : S => d.1) env' (t:=p (p s (a w)) w) Can.first
    have htab : Has m (fun d : S => B d.1) (p (p s (a w)) w) (a w) env'
        (fun d => dotTab (f d.1)) :=
      Can.first.then_do (ht.reindex (fun d : S => d.1))
    exact chirpData_read hh htab l E (fun d => d.2) Can.second
  exact Hwide.bind HC
end Action
end
end FourierSchur.OriginalPhysicalChirpRAM
