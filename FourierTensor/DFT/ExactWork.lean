import FourierTensor.DFT.Program

/-! Integer registers, tape lengths and element locations determine the
execution cost of the exact RAM. Its scalar operations take fixed work
even though their outputs vary with the input. Thus one execution on zero
Fourier data gives the exact work at that length on every complex vector. -/
namespace FourierTensor.AllLengthExactWork

open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

private def Shape : (t : Ty) → t.T → t.T → Prop
  | .w, x, y => x = y
  | .c _, _, _ => True
  | .p s t, x, y => Shape s x.1 y.1 ∧ Shape t x.2 y.2
  | .a t, x, y => x.len = y.len ∧ ∀ (i : ℕ) (h : i<x.len) (k : i<y.len),
      Shape t (x.pos ⟨i,h⟩) (y.pos ⟨i,k⟩)

private theorem shape_refl (s : Ty) (x : s.T) : Shape s x x := by
  induction s with
  | w => rfl
  | c => trivial
  | p s t hs ht => exact ⟨hs _,ht _⟩
  | a t ht => exact ⟨rfl,fun _ _ _ => ht _⟩

private theorem shape_look (s : Ty) {v w' : Tape s.T} (H : Shape (.a s) v w') (i : ℕ) :
    Shape s (v.look i s.blank) (w'.look i s.blank) := by
  obtain ⟨he,H⟩ := H
  by_cases h : i<v.len
  · rw [Tape.look_of_lt _ _ h,Tape.look_of_lt _ _ (he ▸ h)]
    exact H i h (he ▸ h)
  · rw [Tape.look_of_le _ _ (Nat.le_of_not_gt h),Tape.look_of_le _ _ (he ▸ Nat.le_of_not_gt h)]
    exact shape_refl _ _

private theorem shape_set (s : Ty) {v w' : Tape s.T} (H : Shape (.a s) v w') (i : ℕ)
    {x y : s.T} (hxy : Shape s x y) : Shape (.a s) (v.set i x) (w'.set i y) := by
  obtain ⟨he,H⟩ := H
  refine ⟨he,fun l a b => ?_⟩
  by_cases h : l=i
  · simpa only [Tape.set,if_pos h] using hxy
  · simpa only [Tape.set,if_neg h] using H l a b

private def Related {α : Type*} (r : α → α → Prop) (x y : Bill α) : Prop :=
  x.work = y.work ∧ r x.val y.val

private theorem related_one {α : Type*} {r : α → α → Prop} {x y : α} (h : r x y) :
    Related r (Bill.one x) (Bill.one y) := ⟨rfl,h⟩

private theorem related_pay {α : Type*} {r : α → α → Prop} {x y : Bill α}
    (h : Related r x y) (n k : ℕ) : Related r (x.pay n k) (y.pay n k) :=
  ⟨congrArg (· + n) h.1,h.2⟩

private theorem related_pass {α β : Type*} {r : α → α → Prop} {s : β → β → Prop}
    {x y : Bill α} {f g : α → Bill β} (h : Related r x y)
    (k : ∀ a b, r a b → Related s (f a) (g b)) : Related s (x.pass f) (y.pass g) := by
  have H := k _ _ h.2
  exact ⟨congrArg₂ Nat.add h.1 H.1,H.2⟩

private theorem related_steps {α : Type*} {r : α → α → Prop} {x y : α}
    {f g : ℕ → α → Bill α} (h : r x y) (k : ∀ i a b, r a b → Related r (f i a) (g i b))
    (n : ℕ) : Related r (Bill.steps x f n) (Bill.steps y g n) := by
  induction n with
  | zero => exact related_one h
  | succ n ih => exact related_pay (related_pass ih (k n)) _ _

private theorem related_sow (s : Ty) (l n : ℕ) {f g : ℕ → Bill (ℕ × s.T)}
    (h : ∀ i, Related (Shape (.p .w s)) (f i) (g i)) :
    Related (Shape (.a s)) (Bill.sow l n s.blank f) (Bill.sow l n s.blank g) := by
  apply related_pay
  apply related_steps (shape_refl (.a s) _)
  intro i a b hab
  apply related_pass (h i)
  rintro ⟨j,x⟩ ⟨j',y⟩ ⟨(he : j=j'),hx⟩
  subst j'
  exact related_one (shape_set s hab j hx)

private theorem related_tab (s : Ty) (l : ℕ) {f g : ℕ → Bill s.T}
    (h : ∀ i, Related (Shape s) (f i) (g i)) :
    Related (Shape (.a s)) (Bill.tab l s.blank f) (Bill.tab l s.blank g) := by
  apply related_sow
  intro i
  exact related_pass (h i) (fun _ _ hxy => related_one (show Shape (.p .w s) _ _ from ⟨rfl,hxy⟩))

/-- Replace the scalar instructions by a unit-cost write of zero. Integer
instructions and structural operations retain their original semantics. -/
def eraseAtom {a s t} (op : Atom a s t) : Atom a s t :=
  match op with
  | .cone => .cz _
  | .add _ => .cz _
  | .sub _ => .cz _
  | .scale _ => .cz _
  | .inv => .cz _
  | .cross _ => .cz _
  | op => op

/-- A cost evaluator with the same integer instructions, tape accesses,
branches and recursion. It never performs complex arithmetic. -/
def erase {a r s t} : Code a r s t → Code a r s t
  | .atom op => .atom (eraseAtom op)
  | .comp f g => .comp (erase f) (erase g)
  | .fork f g => .fork (erase f) (erase g)
  | .ifz q f g => .ifz (erase q) (erase f) (erase g)
  | .loop n init body => .loop (erase n) (erase init) (erase body)
  | .tab n body => .tab (erase n) (erase body)
  | .sow n count body => .sow (erase n) (erase count) (erase body)
  | .importClosed f => .importClosed (erase f)
  | .call => .call
  | .descend base step => .descend (erase base) (erase step)

private theorem atom_related {allow : Bool} {s t : Ty} (op : Atom allow s t)
    (x y : s.T) (h : Shape s x y) : Related (Shape t) (op.run x) ((eraseAtom op).run y) := by
  cases op with
  | lit => exact ⟨rfl,rfl⟩
  | int f =>
    have he : x=y := Prod.ext h.1 h.2
    subst y
    exact ⟨rfl,rfl⟩
  | cz => exact ⟨rfl,trivial⟩
  | cone => exact ⟨rfl,trivial⟩
  | add => exact ⟨rfl,trivial⟩
  | sub => exact ⟨rfl,trivial⟩
  | scale => exact ⟨rfl,trivial⟩
  | inv => exact ⟨rfl,trivial⟩
  | cross => exact ⟨rfl,trivial⟩
  | id => exact ⟨rfl,h⟩
  | fst => exact ⟨rfl,h.1⟩
  | snd => exact ⟨rfl,h.2⟩
  | len => exact ⟨rfl,h.1⟩
  | @look t =>
    have he : x.2=y.2 := h.2
    refine ⟨rfl,?_⟩
    change Shape t (x.1.look x.2 t.blank) (y.1.look y.2 t.blank)
    rw [he]
    exact shape_look t h.1 _

private def Handlers : (r : Port) → Handler r → Handler r → Prop
  | none, _, _ => True
  | some (s,t), h, k => ∀ x y, Shape s x y → Related (Shape t) (h x) (k y)

private theorem code_related {m r s t} (p : Code m r s t) (h k : Handler r)
    (hh : Handlers r h k) (x y : s.T) (hx : Shape s x y) :
    Related (Shape t) (p.run h x) ((erase p).run k y) := by
  induction p with
  | atom op => exact atom_related op x y hx
  | comp f g hf hg =>
    exact related_pay (related_pass (hf _ _ hh x y hx) (hg _ _ hh)) _ _
  | fork f g hf hg =>
    apply related_pass (hf _ _ hh x y hx)
    intro a b hab
    exact related_pass (hg _ _ hh x y hx) (fun _ _ hcd => related_one ⟨hab,hcd⟩)
  | ifz q f g hq hf hg =>
    apply related_pay
    apply related_pass (hq _ _ hh x y hx)
    intro i j (hij : i=j)
    subst j
    split
    · exact hf _ _ hh x y hx
    · exact hg _ _ hh x y hx
  | loop n init body hn hi hb =>
    apply related_pay
    apply related_pass (hn _ _ hh x y hx)
    intro i j (hij : i=j)
    subst j
    apply related_pass (hi _ _ hh x y hx)
    intro u v huv
    exact related_steps huv (fun a w z hwz => hb _ _ hh (x,(a,w)) (y,(a,z)) ⟨hx,rfl,hwz⟩) i
  | @tab r s t n body hn hb =>
    apply related_pay
    apply related_pass (hn _ _ hh x y hx)
    intro i j (hij : i=j)
    subst j
    exact related_tab t i (fun a => hb _ _ hh _ _ ⟨hx,rfl⟩)
  | @sow r s t n count body hn hc hb =>
    apply related_pay
    apply related_pass (hn _ _ hh x y hx)
    intro i j (hij : i=j)
    subst j
    apply related_pass (hc _ _ hh x y hx)
    intro u v (huv : u=v)
    subst v
    exact related_sow t i u (fun a => hb _ _ hh _ _ ⟨hx,rfl⟩)
  | importClosed f hf => exact related_pay (hf () () trivial x y hx) _ _
  | call => exact related_pay (hh x y hx) _ _
  | @descend r s t base step hb hs =>
    have hr (n : ℕ) : Handlers (some (s,t)) (depthRun (base.run ()) step.run n)
        (depthRun ((erase base).run ()) (erase step).run n) := by
      induction n with
      | zero => exact fun v w hv => related_pay (hb () () trivial v w hv) _ _
      | succ n ih => exact fun v w hv => related_pay (hs _ _ ih v w hv) _ _
    rcases x with ⟨i,v⟩
    rcases y with ⟨j,w⟩
    obtain ⟨(hij : i=j),hvw⟩ := hx
    subst j
    exact related_pay (hr i v w hvw) _ _

/-- Integer and tape operations alone determine the exact cost of a solver. -/
theorem solve_erased_work (solve : Prog false dftInKind dftOutKind) (n : ℕ)
    (r : ℂ) (x : Vec n) :
    (run solve (n,r,(⟨n,x⟩ : Tape ℂ))).work =
      (run (erase solve) (n,(0:ℂ),(⟨n,fun _ => 0⟩ : Tape ℂ))).work :=
  (code_related solve () () trivial
    (n,r,(⟨n,x⟩ : Tape ℂ)) (n,(0:ℂ),(⟨n,fun _ => 0⟩ : Tape ℂ))
    ⟨rfl,trivial,rfl,fun _ _ _ => trivial⟩).1

/-- The work counter of a fixed DFT solver on an order and a vector depends
only on their integer and array shapes. -/
theorem solve_work_eq (solve : Prog false dftInKind dftOutKind) (n : ℕ) (r s : ℂ)
    (x y : Vec n) :
    (run solve (n,r,(⟨n,x⟩ : Tape ℂ))).work = (run solve (n,s,(⟨n,y⟩ : Tape ℂ))).work :=
  (solve_erased_work solve n r x).trans (solve_erased_work solve n s y).symm

/-- Actual work at length `n`, evaluated on zero complex input. -/
def work (order : Prog false w w) (solve : Prog false dftInKind dftOutKind) (n : ℕ) : ℕ :=
  (run order n).work + 1 + (run solve (n,root (run order n).val,(⟨n,fun _ => 0⟩ : Tape ℂ))).work

/-- An equivalent length-only count. Both programs run with scalar
instructions erased, and the root is represented only by its unit charge. -/
def count (order : Prog false w w) (solve : Prog false dftInKind dftOutKind) (n : ℕ) : ℕ :=
  (run (erase order) n).work + 1 +
    (run (erase solve) (n,(0:ℂ),(⟨n,fun _ => 0⟩ : Tape ℂ))).work

theorem work_eq_count (order : Prog false w w) (solve : Prog false dftInKind dftOutKind)
    (n : ℕ) : work order solve n = count order solve n := by
  unfold work count
  rw [(code_related order () () trivial n n rfl).1, solve_erased_work]

theorem work_eq (order : Prog false w w) (solve : Prog false dftInKind dftOutKind)
    (n : ℕ) (x : Vec n) :
    (run order n).work + 1 + (run solve (n,root (run order n).val,(⟨n,x⟩ : Tape ℂ))).work =
      work order solve n := by
  unfold work
  rw [solve_work_eq solve n _ (root (run order n).val) x (fun _ => 0)]

theorem work_le_of_contract {order : Prog false w w} {solve : Prog false dftInKind dftOutKind}
    {W : ℕ → ℕ} (h : DFTProgram order solve W) (n : ℕ) (hn : 0<n) :
    work order solve n ≤ W n := by
  obtain ⟨_,H⟩ := h
  exact ((H n hn).2.2.2.2.2.2 (fun _ => 0)).2.2.1

/-- The same programs satisfy the upstream DFT specification with their
actual work in place of any previously certified upper allowance. -/
theorem exact_contract {order : Prog false w w} {solve : Prog false dftInKind dftOutKind}
    {W : ℕ → ℕ} (h : DFTProgram order solve W) : DFTProgram order solve (work order solve) := by
  obtain ⟨p,H⟩ := h
  refine ⟨p,fun n hn => ?_⟩
  obtain ⟨hcap,hpeak,hvalid,hpos,hub,hrec,hx⟩ := H n hn
  have hw := work_le_of_contract (order:=order) (solve:=solve) (W:=W) ⟨p,H⟩ n hn
  refine ⟨(Nat.add_le_add_right hw _).trans hcap,hpeak,hvalid,hpos,hub,hrec,fun x => ?_⟩
  have Hx := hx x
  exact ⟨Hx.1,Hx.2.1,(work_eq order solve n x).le,Hx.2.2.2⟩

end
end FourierTensor.AllLengthExactWork
