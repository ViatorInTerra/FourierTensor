import vendor.OpenAIUniformFourierBundle

/-!
A paid RAM adapter for one complete residual tensor block.  A fixed binary
change of column basis splits selected coordinates from spectator coordinates;
each spectator obtains one complete child call of order `Y.n * f`.  Gathering,
allocation, address generation, and scattering use the native RAM combinators.
The open-call charge is additive, with no hidden multiplier on child work.
-/
namespace OAI.PowerSaving.RAM.GroupedResidual
open OAI PowerSaving Binary Matrix Ty Finset
noncomputable section

universe U
variable {α β γ : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

/-- Explicit fixed binary matrices implementing both directions of a basis
address change.  The matrices are code constants; the data addresses are paid. -/
structure ColumnRoute (α β γ : Type*) [Fintype α] [Fintype β] [Fintype γ] where
  equiv : Space α ≃ Space (β ⊕ γ)
  forward : Matrix (β ⊕ γ) α F
  backward : Matrix α (β ⊕ γ) F
  forward_eq : ∀ x, equiv x = forward.mulVec x
  backward_eq : ∀ x, equiv.symm x = backward.mulVec x
  card_eq : Fintype.card α = Fintype.card β + Fintype.card γ

namespace ColumnRoute

/-- Full coordinates in a given orthonormal binary basis. -/
def basisCoordinates (A : OBase α) : Space α ≃ Space α := by
  let M : Matrix α α F := Matrix.of A.v
  have h : M*Mᵀ=1 := by
    ext i j; simpa [M,Matrix.mul_apply,Matrix.one_apply,dot] using A.rows i j
  have h' : Mᵀ*M=1 := mul_eq_one_comm.mp h
  exact
    { toFun := M.mulVec
      invFun := Mᵀ.mulVec
      left_inv := fun x => by rw [Matrix.mulVec_mulVec,h',Matrix.one_mulVec]
      right_inv := fun x => by rw [Matrix.mulVec_mulVec,h,Matrix.one_mulVec] }

/-- Every fixed orthonormal basis and partition has explicit paid address
matrices. This constructor supplies the route, rather than assuming a routing
oracle for an independent family. -/
def ofOBase (A : OBase α) (j : (β ⊕ γ) ≃ α) : ColumnRoute α β γ where
  equiv := (basisCoordinates A).trans (Layout.permFn j.symm F)
  forward := fun row col => A.v (j row) col
  backward := fun col row => A.v (j row) col
  forward_eq x := rfl
  backward_eq x := by
    funext a
    change (∑ b : α, A.v b a * x (j.symm b)) =
      ∑ b : β ⊕ γ, A.v (j b) a * x b
    rw [← Equiv.sum_comp j]
    simp
  card_eq := by
    have h := Fintype.card_congr j
    rw [Fintype.card_sum] at h
    exact h.symm

/-- The selected set and its actual complement partition the full basis. -/
def subsetPartition (t : Finset α) :
    ({j : α // j ∈ t} ⊕ {j : α // j ∉ t}) ≃ α where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun j := if h : j ∈ t then Sum.inl ⟨j,h⟩ else Sum.inr ⟨j,h⟩
  left_inv j := by cases j with
    | inl j => simp [j.property]
    | inr j => simp [j.property]
  right_inv j := by dsimp; split <;> rfl

def forSubset (A : OBase α) (t : Finset α) :
    ColumnRoute α {j : α // j ∈ t} {j : α // j ∉ t} :=
  ofOBase A (subsetPartition t)

end ColumnRoute

variable (e : ColumnRoute α β γ) (X : Layout α) (Y : Layout β) (Z : Layout γ)

/-- Selected columns have their actual transposed-column address order. -/
def selectedIndex (f : ℕ) : Sky β f ≃ Bits (Y.n * f) :=
  let empty : Bits 0 := fun j => Fin.elim0 j
  { toFun := fun x => serial Y 0 f (by omega) (empty,x)
    invFun := fun x => ((serial Y 0 f (by omega)).symm x).2
    left_inv := fun x => by simp
    right_inv := fun x => by
      calc
        _ = (serial Y 0 f (k:=Y.n*f) (by omega))
            ((serial Y 0 f (k:=Y.n*f) (by omega)).symm x) := by
          change (serial Y 0 f (k:=Y.n*f) (by omega))
            (empty,((serial Y 0 f (k:=Y.n*f) (by omega)).symm x).2) = _
          apply congr_arg (serial Y 0 f (k:=Y.n*f) (by omega))
          apply Prod.ext
          · funext j; exact Fin.elim0 j
          · rfl
        _ = x := (serial Y 0 f (k:=Y.n*f) (by omega)).apply_symm_apply x }

lemma selected_code (f : ℕ) (x : Sky β f) :
    (bits (Y.n*f)).loc (selectedIndex Y f x) = (bodyOrder Y f).loc x := by
  simpa [selectedIndex,book,Layout.pair,bits_loc] using
    serial_code Y 0 f (k:=Y.n*f) (by omega) ((fun j => Fin.elim0 j),x)

/-- Spectator address first, selected tensor address second. -/
def split (r f : ℕ) : Grid α r f ≃ (Grid γ r f × Bits (Y.n*f)) where
  toFun x := ((x.1,fun j c => e.equiv (x.2 j) (.inr c)),
    selectedIndex Y f (fun j b => e.equiv (x.2 j) (.inl b)))
  invFun x := (x.1.1,fun j => e.equiv.symm
    (Sum.elim ((selectedIndex Y f).symm x.2 j) (x.1.2 j)))
  left_inv x := by
    dsimp
    congr 1
    funext j
    simp only [Equiv.symm_apply_apply]
    have h : Sum.elim (fun b => e.equiv (x.2 j) (.inl b))
        (fun c => e.equiv (x.2 j) (.inr c)) = e.equiv (x.2 j) := by
      funext q; cases q <;> rfl
    rw [h]; exact e.equiv.symm_apply_apply _
  right_inv x := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext j c
        dsimp
        rw [Equiv.apply_symm_apply]
        rfl
    · change (selectedIndex Y f)
        (fun j b => e.equiv (e.equiv.symm
          (Sum.elim ((selectedIndex Y f).symm x.2 j) (x.1.2 j))) (.inl b)) = x.2
      simp only [Equiv.apply_symm_apply,Sum.elim_inl]

def childInput (r f : ℕ) (v : Grid α r f → ℂ) (p : Grid γ r f) :
    Bits (Y.n*f) → ℂ := fun q => v ((split e Y r f).symm (p,q))

def result (r f : ℕ) (v : Grid α r f → ℂ) : Grid α r f → ℂ :=
  fun x => ripple (Y.n*f) (childInput e Y r f v ((split e Y r f x).1))
    ((split e Y r f x).2)

include e in
lemma mass (r f : ℕ) : (book Z r f).n * (bits (Y.n*f)).n = (book X r f).n := by
  have h : X.n=Y.n+Z.n := by
    rw [← X.card,← Y.card,← Z.card]; exact e.card_eq
  change (2^r*(2^f)^Z.n)*2^(Y.n*f)=2^r*(2^f)^X.n
  rw [h,pow_add,Nat.mul_comm Y.n,pow_mul]
  ac_rfl

section Address
variable {ι : Type U} {m : Bool} {B f : ι → ℕ} {s : Ty} {x : ι → T s}
  (g : Gear m B f s x)
include g

/-- A fixed finite XOR reduction costs constant native word work. -/
lemma sum_bits {δ : Type*} [Fintype δ] (v : δ → ∀ i, Bits (f i))
    (h : ∀ j, Knows m B s x (fun i => (bits (f i)).loc (v j i))) :
    Knows m B s x (fun i => (bits (f i)).loc (∑ j, v j i)) := by
  classical
  have hh (a : Finset δ) :
      Knows m B s x (fun i => (bits (f i)).loc (∑ j ∈ a, v j i)) := by
    induction a using Finset.induction with
    | empty =>
      refine (Can.wc 0).cong (fun _ => rfl) ?_
      intro i; simp [bits_loc]
    | insert j a hj ih =>
      simpa [hj] using g.addr_xor (fun i => (v j i,∑ k ∈ a,v k i)) (h j) ih
  exact hh univ

/-- Fixed binary matrix rows operate on whole `f`-bit column groups using the
prepared XOR table. No input bit or spectator is omitted. -/
lemma linear_column {δ ε : Type*} [Fintype δ] [Fintype ε]
    (D : Layout δ) (E : Layout ε) (M : Matrix ε δ F)
    (v : ∀ i, Sky δ (f i))
    (h : Knows m B s x fun i => (bodyOrder D (f i)).loc (v i)) :
    Knows m B s x fun i =>
      (bodyOrder E (f i)).loc (fun j => M.mulVec (v i j)) := by
  classical
  apply g.body_set E
  intro q
  have hq := sum_bits g (fun a i j => M q a * v i j a) (fun a => ?_)
  · refine hq.cong (fun _ => rfl) ?_
    intro i; congr 1; funext j; simp [Matrix.mulVec, dotProduct,Finset.sum_apply]
  · rcases bit_cases (M q a) with hm|hm
    · refine (Can.wc 0).cong (fun _ => rfl) ?_
      intro i; simp [hm,bits_loc]
    · simpa [hm] using g.body_get D v a h

lemma selected_size : Knows m B s x fun i => (bits (Y.n*f i)).n := by
  refine (g.body_size Y).cong (fun _ => rfl) ?_
  intro i; change (2^f i)^Y.n=2^(Y.n*f i); rw [← pow_mul,Nat.mul_comm]

lemma selected_small : Small B fun i => (bits (Y.n*f i)).n := by
  refine (g.body_small Y).mono ?_
  intro i; change 2^(Y.n*f i)≤(2^f i)^Y.n
  rw [← pow_mul,Nat.mul_comm]

/-- Paid original-address to (spectator, selected) addresses. -/
lemma split_addresses (r : ℕ) (v : ∀ i, Grid α r (f i))
    (h : Knows m B s x fun i => (book X r (f i)).loc (v i)) :
    Knows m B s x (fun i => (book Z r (f i)).loc (split e Y r (f i) (v i)).1) ∧
    Knows m B s x (fun i => (bits (Y.n*f i)).loc (split e Y r (f i) (v i)).2) := by
  obtain ⟨ht,hv⟩ := g.grid_fetch X r h
  let a i j := e.equiv ((v i).2 j)
  have hrow (q : β ⊕ γ) :
      Knows m B s x fun i => (bits (f i)).loc (fun j => a i j q) := by
    have H := linear_column g X (Layout.someLayout (β ⊕ γ)) e.forward
      (fun i => (v i).2) hv
    have K := g.body_get (Layout.someLayout (β ⊕ γ))
      (fun i j => e.forward.mulVec ((v i).2 j)) q H
    refine K.cong (fun _ => rfl) ?_
    intro i; simp [a,e.forward_eq]
  refine ⟨g.grid_combine Z r ht (g.body_set Z _ (fun c => hrow (.inr c))),?_⟩
  have H := g.body_set Y (fun i j b => a i j (.inl b)) (fun b => hrow (.inl b))
  refine H.cong (fun _ => rfl) ?_
  intro i; exact (selected_code Y _ _).symm

/-- Paid inverse basis routing from independent spectator/selected addresses. -/
lemma merge_address (r : ℕ) (v : ∀ i, Grid γ r (f i) × Bits (Y.n*f i))
    (hs : Knows m B s x fun i => (book Z r (f i)).loc (v i).1)
    (ht : Knows m B s x fun i => (bits (Y.n*f i)).loc (v i).2) :
    Knows m B s x fun i => (book X r (f i)).loc ((split e Y r (f i)).symm (v i)) := by
  obtain ⟨hp,hz⟩ := g.grid_fetch Z r hs
  let a i j := Sum.elim ((selectedIndex Y (f i)).symm (v i).2 j) ((v i).1.2 j)
  have hy : Knows m B s x fun i =>
      (bodyOrder Y (f i)).loc ((selectedIndex Y (f i)).symm (v i).2) := by
    refine ht.cong (fun _ => rfl) ?_
    intro i; simpa using selected_code Y (f i) ((selectedIndex Y (f i)).symm (v i).2)
  have ha : Knows m B s x fun i =>
      (bodyOrder (Layout.someLayout (β ⊕ γ)) (f i)).loc (a i) := by
    apply g.body_set
    intro q; cases q with
    | inl b => exact g.body_get Y _ b hy
    | inr c => exact g.body_get Z _ c hz
  have H := linear_column g (Layout.someLayout (β ⊕ γ)) X e.backward a ha
  refine g.grid_combine X r hp (H.cong (fun _ => rfl) ?_)
  intro i; simp [split,a,e.backward_eq]

end Address

section Execution
variable {ι : Type U} {m : Bool} {B f : ι → ℕ} {s : Ty} {x : ι → T s}
  {cl : Paint} {r : ℕ} {v : ∀ i, Grid α r (f i) → ℂ}

/-- Prepared metadata and the complete arbitrary input array. -/
structure Rig (m : Bool) (B f : ι → ℕ) (s : Ty) (x : ι → T s)
    (cl : Paint) (X : Layout α) (r : ℕ) (v : ∀ i, Grid α r (f i) → ℂ) : Prop where
  gear : Gear m B f s x
  imag : Has m B s sc x (fun _ => Complex.I)
  items : Has m B s (bundle cl) x (fun i => (book X r (f i)).tape (v i))

namespace Rig
variable {X}
variable (h : Rig m B f s x cl X r v)
include h

lemma gather {κ : Type*} {t : Ty} (j : κ → ι) (y : κ → T t)
    (H : Has m (fun k => B (j k)) t s y (fun k => x (j k))) :
    Rig m (fun k => B (j k)) (fun k => f (j k)) t y cl X r
      (fun k => v (j k)) :=
  ⟨h.gear.descend j y H,H.then_do (h.imag.reindex j),
    H.then_do (h.items.reindex j)⟩

lemma selected_order : Knows m B s x fun i => Y.n*f i :=
  ((Can.wc Y.n).times h.gear.given (Small.const B Y.n)
    (h.gear.bound.mono (fun i => Nat.lt_two_pow_self.le)))

/-- The fixed translation compensating inverse direction factors is a real
full-width native pass, including every address calculation and array read. -/
lemma shift_cost (z : Space α) :
    Can m B s (bundle cl) x
      (fun i => (book X r (f i)).tape
        (fun a => v i (a.1,fun j => a.2 j+z)))
      (fun i => (book X r (f i)).n) := by
  let J := Σ i, Grid α r (f i)
  let env (d : J) : T (Ty.p s Ty.w) := (x d.1,(book X r (f d.1)).loc d.2)
  have G := h.gather (Sigma.fst (β:=fun i => Grid α r (f i))) env Can.first
  have HA := G.gear.shifted X r z (fun d => d.2) Can.second
  have HR := Can.fetch (t:=c cl) (L:=fun d : J => book X r (f d.1))
    (v:=fun d => v d.1) (i:=fun d => (d.2.1,fun j => d.2.2 j+z)) G.items HA
  have HT := Can.layout (L:=fun i => book X r (f i))
    (v:=fun i a => v i (a.1,fun j => a.2 j+z)) (t:=c cl) (P:=fun _ => 0)
    (h.gear.grid_size X r) HR (h.gear.grid_small X r)
  simpa only [Nat.zero_add,Nat.mul_zero,Nat.add_zero] using HT

lemma fill_read (p : ∀ i, Grid γ r (f i)) (q : ∀ i, Bits (Y.n*f i))
    (hp : Knows m B s x fun i => (book Z r (f i)).loc (p i))
    (hq : Knows m B s x fun i => (bits (Y.n*f i)).loc (q i)) :
    Has m B s (c cl) x fun i => childInput e Y r (f i) (v i) (p i) (q i) := by
  exact Can.fetch (t:=c cl) (L:=fun i => book X r (f i)) (v:=v)
    (i:=fun i => (split e Y r (f i)).symm (p i,q i))
    h.items (merge_address e X Y Z h.gear r (fun i => (p i,q i)) hp hq)

/-- Allocate and fill one complete selected tensor. Every lane is fetched from
its actual source address, including its spectator coordinates. -/
lemma fill_ready (p : ∀ i, Grid γ r (f i))
    (hp : Knows m B s x fun i => (book Z r (f i)).loc (p i)) :
    Can m B s (simIn cl) x
      (fun i => givenBits cl (Y.n*f i) (childInput e Y r (f i) (v i) (p i)))
      (fun i => (bits (Y.n*f i)).n) := by
  let W i := (bits (Y.n*f i)).n
  let V i := childInput e Y r (f i) (v i) (p i)
  let J := Σ i, Bits (Y.n*f i)
  let env (d : J) : T (Ty.p s Ty.w) := (x d.1,(bits (Y.n*f d.1)).loc d.2)
  have G := h.gather (Sigma.fst (β:=fun i => Bits (Y.n*f i))) env Can.first
  have HH := G.fill_read e Y Z (fun d => p d.1) (fun d => d.2)
    (Can.first.then_do (hp.reindex (Sigma.fst (β:=fun i => Bits (Y.n*f i)))))
    Can.second
  have HT := Can.layout (L:=fun i => bits (Y.n*f i)) (v:=V) (t:=c cl)
    (P:=fun _ => 0) (selected_size Y h.gear) HH (selected_small Y h.gear)
  have HD : Can m B s (bundle cl) x (fun i => (bits (Y.n*f i)).tape (V i)) W := by
    simpa [W] using HT
  exact (h.selected_order Y |>.mono (fun _ => Nat.zero_le _)).pair
    ((h.imag.mono (fun _ => Nat.zero_le _)).pair HD)

/-- Read one output coordinate from the independent returned child arrays.
Both levels of addressing and both array reads are paid native operations. -/
lemma scatter_read
    (H : Has m B s (a (bundle cl)) x fun i => (book Z r (f i)).tape
      (fun p => (bits (Y.n*f i)).tape (ripple (Y.n*f i)
        (childInput e Y r (f i) (v i) p))))
    (a : ∀ i, Grid α r (f i))
    (ha : Knows m B s x fun i => (book X r (f i)).loc (a i)) :
    Has m B s (c cl) x fun i => result e Y r (f i) (v i) (a i) := by
  obtain ⟨hs,ht⟩ := split_addresses e X Y Z h.gear r a ha
  have HH := Can.fetch (t:=bundle cl) (L:=fun i => book Z r (f i))
    (v:=fun i p => (bits (Y.n*f i)).tape (ripple (Y.n*f i)
      (childInput e Y r (f i) (v i) p)))
    (i:=fun i => (split e Y r (f i) (a i)).1) H hs
  exact Can.fetch (t:=c cl) (L:=fun i => bits (Y.n*f i))
    (v:=fun i => ripple (Y.n*f i)
      (childInput e Y r (f i) (v i) (split e Y r (f i) (a i)).1))
    (i:=fun i => (split e Y r (f i) (a i)).2) HH ht

/-- Complete native adapter around a uniform genuine child program. Local
gather/scatter work is linear in the full tensor width. Its extra local child
work is multiplied by the exact number of spectators, and the external charge
is *only additive*. -/
lemma run_with {port : Port} (b : Bank port ι) (hB : b.B=B)
    (η τ : ι → ℕ)
    (child : Able m (b.comap (Sigma.fst (β:=fun i => Grid γ r (f i))))
      (simIn cl) (bundle cl)
      (fun d => givenBits cl (Y.n*f d.1)
        (childInput e Y r (f d.1) (v d.1) d.2))
      (fun d => (bits (Y.n*f d.1)).tape (ripple (Y.n*f d.1)
        (childInput e Y r (f d.1) (v d.1) d.2)))
      (fun d => η d.1) (fun d => τ d.1)) :
    Able m b s (bundle cl) x (fun i => (book X r (f i)).tape
      (result e Y r (f i) (v i)))
      (fun i => (book X r (f i)).n+(book Z r (f i)).n*η i)
      (fun i => (book Z r (f i)).n*τ i) := by
  subst B
  let W i := (book X r (f i)).n+(book Z r (f i)).n*η i
  let P i := (book Z r (f i)).n
  let S i := (bits (Y.n*f i)).n
  let J := Σ i, Grid γ r (f i)
  let ans i p := (bits (Y.n*f i)).tape (ripple (Y.n*f i)
    (childInput e Y r (f i) (v i) p))
  let yields i := (book Z r (f i)).tape (ans i)
  let env (d : J) : T (Ty.p s Ty.w) := (x d.1,(book Z r (f d.1)).loc d.2)
  have G := h.gather (Sigma.fst (β:=fun i => Grid γ r (f i))) env Can.first
  have HC := G.fill_ready e Y Z (fun d => d.2) Can.second
  have HU := (Able.of_can (b:=b.comap (Sigma.fst (β:=fun i => Grid γ r (f i)))) HC).comp child
  have HU' : Able m (b.comap (Sigma.fst (β:=fun i => Grid γ r (f i))))
      (Ty.p s Ty.w) (bundle cl) env (fun d => ans d.1 d.2)
      (fun d => S d.1+η d.1) (fun d => τ d.1) := by
    simpa only [Nat.zero_add] using HU
  have HN : Able m b s Ty.w x P (fun _ => 0) (fun _ => 0) :=
    Able.of_can (h.gear.grid_size Z r)
  have HY := Able.layout (L:=fun i => book Z r (f i)) (v:=ans)
    (t:=bundle cl) (P:=fun i => S i+η i) (H:=τ) HN HU'
    (h.gear.grid_small Z r)
  have HNle (i) : P i ≤ (book X r (f i)).n := by
    have H := mass e X Y Z r (f i)
    have HS : 0<S i := by dsimp [S]; change 0<2^(Y.n*f i); positivity
    exact (Nat.le_mul_of_pos_right _ HS).trans (le_of_eq H)
  have HY' : Able m b s (a (bundle cl)) x yields W (fun i => P i*τ i) := by
    refine HY.weaken ⟨3,fun i => ?_⟩ (fun i => by
      change 0+P i*τ i≤P i*τ i
      omega)
    change 0+P i+P i*(S i+η i)+1 ≤ 3*(W i+1)
    have H := mass e X Y Z r (f i)
    change P i*S i=(book X r (f i)).n at H
    have HP := HNle i
    dsimp [W]
    rw [Nat.mul_add,H]
    dsimp only [P] at HP ⊢
    omega
  let t := Ty.p s (a (bundle cl))
  let outenv i : T t := (x i,yields i)
  have GG := h.gather id outenv Can.first
  let Q := Σ i, Grid α r (f i)
  let rowenv (d : Q) : T (Ty.p t Ty.w) := (outenv d.1,(book X r (f d.1)).loc d.2)
  have RG := GG.gather (Sigma.fst (β:=fun i => Grid α r (f i))) rowenv Can.first
  have HR := RG.scatter_read e Y Z (Can.snd Can.first) (fun d => d.2) Can.second
  have HT := Can.layout (L:=fun i => book X r (f i))
    (v:=fun i => result e Y r (f i) (v i)) (t:=c cl) (P:=fun _ => 0)
    (GG.gear.grid_size X r) HR (GG.gear.grid_small X r)
  have HS : Can m b.B t (bundle cl) outenv
      (fun i => (book X r (f i)).tape (result e Y r (f i) (v i))) W := by
    refine HT.mono ?_
    intro i; simp only [Nat.zero_add,Nat.mul_zero,Nat.add_zero]
    exact Nat.le_add_right _ _
  simpa only [Nat.add_zero] using HY'.save_keep (Able.of_can HS)

/-- Raw one-array child contract: it must work on arbitrary complex input. -/
def RawContract (cl : Paint) (b : Bank (hatch cl) ι) (k τ : ι → ℕ) : Prop :=
  ∀ i v, (b.use i (givenBits cl (k i) v)).OK
    ((bits (k i)).tape (ripple (k i) v)) (τ i) (b.ext i)

lemma run_open (b : Bank (hatch cl) ι) (hB : b.B=B) (τ : ι → ℕ)
    (hc : RawContract cl b (fun i => Y.n*f i) τ) :
    Able m b s (bundle cl) x (fun i => (book X r (f i)).tape
      (result e Y r (f i) (v i)))
      (fun i => (book X r (f i)).n)
      (fun i => (book Z r (f i)).n*τ i) := by
  have H := h.run_with e Y Z b hB (fun _ => 0) τ
    (Able.use_call (fun d => hc d.1 _))
  simpa [Nat.mul_zero,Nat.add_zero] using H

include Z in
/-- Closed instantiation calls the existing power-saving hills program, not a
scalar butterfly replacement. All spectators and all returned coordinates are
charged. -/
lemma run_closed :
    Can m B s (bundle cl) x (fun i => (book X r (f i)).tape
      (result e Y r (f i) (v i)))
      (fun i => (book X r (f i)).n * (hills (Y.n*f i)+1)) := by
  let J := Σ i, Grid γ r (f i)
  let V (d : J) := childInput e Y r (f d.1) (v d.1) d.2
  have HC := hills_program cl m (fun d : J => Y.n*f d.1) V
  have HS := (selected_small Y h.gear).reindex (Sigma.fst (β:=fun i => Grid γ r (f i)))
  have H := h.run_with e Y Z (Bank.closed B) rfl
    (fun i => (bits (Y.n*f i)).n*hills (Y.n*f i)) (fun _ => 0)
    (HC.ambient HS)
  have HE (i) : (book X r (f i)).n +
      (book Z r (f i)).n*((bits (Y.n*f i)).n*hills (Y.n*f i)) =
      (book X r (f i)).n*(hills (Y.n*f i)+1) := by
    rw [← Nat.mul_assoc,mass e X Y Z r (f i)]; ring
  simpa only [HE,Nat.mul_zero] using H

end Rig

/-- Public raw-grid input: the header provides the current column length f.
There are no precomputed address tables in this input. -/
def givenGrid (cl : Paint) (X : Layout α) (r f : ℕ) (v : Grid α r f → ℂ) :
    T (simIn cl) := (f,Complex.I,(book X r f).tape v)

include X Y Z e in
/-- Metadata preparation, all fiber calls, and final scatter in one native open
program. The `3 ≤ X.n` assumption pays for the native XOR-table constructor's
`2^(3f)` operations in the full tensor width. -/
lemma run_open_grid (b : Bank (hatch cl) ι) (τ : ι → ℕ)
    (hr : 3≤X.n) (hB : Small b.B (fun i => (book X r (f i)).n))
    (hc : Rig.RawContract cl b (fun i => Y.n*f i) τ) :
    Able m b (simIn cl) (bundle cl)
      (fun i => givenGrid cl X r (f i) (v i))
      (fun i => (book X r (f i)).tape (result e Y r (f i) (v i)))
      (fun i => (book X r (f i)).n)
      (fun i => (book Z r (f i)).n*τ i) := by
  let W i := (book X r (f i)).n
  let env i := givenGrid cl X r (f i) (v i)
  have hf (i) : f i ≤ X.n*f i+r := by
    have H := Nat.le_mul_of_pos_left (f i) (show 0<X.n by omega)
    omega
  have hpower (i) : 2^f i≤W i := by
    dsimp [W]; rw [book_len]
    exact Nat.pow_le_pow_right (by omega) (hf i)
  have hlen (i) : f i≤W i := Nat.lt_two_pow_self.le.trans (hpower i)
  have sq : Small b.B f := hB.mono hlen
  have hm : Small b.B (fun i => 2^f i) := hB.mono hpower
  have hcube (i) : (2^f i)^3≤W i := by
    dsimp [W]; rw [book_len,← pow_mul]
    apply Nat.pow_le_pow_right (by omega)
    have H := Nat.mul_le_mul_right (f i) hr
    omega
  have HG : Can m b.B (simIn cl) Ty.w env f W := Can.first
  have HP : Can m b.B (simIn cl) (Ty.p Ty.w Ty.w) env
      (fun i => (f i,2^f i)) W :=
    HG.pair (HG.wTwo sq hm (Dom.of_le hlen))
  let T1 := Ty.p (simIn cl) (Ty.p Ty.w Ty.w)
  let env1 (i : ι) : T T1 := (env i,f i,2^f i)
  have HX : Can m b.B T1 (Ty.a Ty.w) env1 (fun i => xorTab (f i)) W :=
    (Can.xor_prepare (m:=m) (f:=f) (B:=b.B) (s:=T1) (x:=env1)
      (Can.fst Can.second) (Can.snd Can.second) sq hm).mono hcube
  let T2 := Ty.p T1 (Ty.a Ty.w)
  let env2 (i : ι) : T T2 := (env1 i,xorTab (f i))
  have HR : Rig m b.B f T2 env2 cl X r v := by
    have H : Has m b.B T2 (simIn cl) env2 env := Can.fst Can.first
    refine ⟨⟨Can.snd (Can.snd Can.first),Can.fst (Can.snd Can.first),Can.second,hm⟩,
      H.snd.fst,H.snd.snd⟩
  have HO := HR.run_open e Y Z b rfl τ hc
  have HT := (Able.of_can (b:=b) HP).save_keep
    ((Able.of_can (b:=b) HX).save_keep HO)
  simpa only [Nat.zero_add] using HT

include X Y Z e in
/-- Fully closed raw-grid adapter, using the native hills backend at the entire
selected order. This preserves its certified power-saving profile. -/
lemma run_closed_grid (hr : 3≤X.n)
    (hB : Small B (fun i => (book X r (f i)).n)) :
    Can m B (simIn cl) (bundle cl)
      (fun i => givenGrid cl X r (f i) (v i))
      (fun i => (book X r (f i)).tape (result e Y r (f i) (v i)))
      (fun i => (book X r (f i)).n*(hills (Y.n*f i)+1)) := by
  let W i := (book X r (f i)).n
  let env i := givenGrid cl X r (f i) (v i)
  have hf (i) : f i ≤ X.n*f i+r := by
    have H := Nat.le_mul_of_pos_left (f i) (show 0<X.n by omega)
    omega
  have hpower (i) : 2^f i≤W i := by
    dsimp [W]; rw [book_len]
    exact Nat.pow_le_pow_right (by omega) (hf i)
  have hlen (i) : f i≤W i := Nat.lt_two_pow_self.le.trans (hpower i)
  have sq : Small B f := hB.mono hlen
  have hm : Small B (fun i => 2^f i) := hB.mono hpower
  have hcube (i) : (2^f i)^3≤W i := by
    dsimp [W]; rw [book_len,← pow_mul]
    apply Nat.pow_le_pow_right (by omega)
    have H := Nat.mul_le_mul_right (f i) hr
    omega
  have HG : Can m B (simIn cl) Ty.w env f W := Can.first
  have HP : Can m B (simIn cl) (Ty.p Ty.w Ty.w) env
      (fun i => (f i,2^f i)) W :=
    HG.pair (HG.wTwo sq hm (Dom.of_le hlen))
  let T1 := Ty.p (simIn cl) (Ty.p Ty.w Ty.w)
  let env1 (i : ι) : T T1 := (env i,f i,2^f i)
  have HX : Can m B T1 (Ty.a Ty.w) env1 (fun i => xorTab (f i)) W :=
    (Can.xor_prepare (m:=m) (f:=f) (B:=B) (s:=T1) (x:=env1)
      (Can.fst Can.second) (Can.snd Can.second) sq hm).mono hcube
  let T2 := Ty.p T1 (Ty.a Ty.w)
  let env2 (i : ι) : T T2 := (env1 i,xorTab (f i))
  have HR : Rig m B f T2 env2 cl X r v := by
    have H : Has m B T2 (simIn cl) env2 env := Can.fst Can.first
    refine ⟨⟨Can.snd (Can.snd Can.first),Can.fst (Can.snd Can.first),Can.second,hm⟩,
      H.snd.fst,H.snd.snd⟩
  have HO := HR.run_closed e Y Z
  have HD : Dom (fun i => W i*(hills (Y.n*f i)+1)) W :=
    Dom.of_le (fun i => Nat.le_mul_of_pos_right _ (by omega))
  exact (HP.weaken HD).bind ((HX.weaken HD).bind HO)

end Execution
end
end OAI.PowerSaving.RAM.GroupedResidual
