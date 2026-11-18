import work_in_progress.OriginalGroupedRoleBitsRAM

/-! Exact address and tensor semantics for the physical role bits, remainder
bits, and grouped column bits. The role banks partition the input; no input is
duplicated to manufacture auxiliary role values. -/
namespace FourierSchur.OriginalGroupedPhysicalBits
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OriginalGroupedRoleBitsRAM
open Matrix Finset
open scoped BigOperators
noncomputable section
variable {α ρ : Type*} [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ]

def physicalBuild (e : ρ ≃ Bits a) (r f : Nat) :
    Beach α ρ r f ≃ Space (Layers α r f ⊕ Fin a) where
  toFun q := Sum.elim (build α r f q.2) (e q.1)
  invFun q := (e.symm (fun j => q (.inr j)),
    (build α r f).symm (fun j => q (.inl j)))
  left_inv q := by simp
  right_inv q := by funext j; cases j <;> simp

def physicalSerial (X : Layout α) (R : Layout ρ) (a r f k : Nat)
    (hR : R.n=2^a) (hk : X.n*f+r+a=k) : Beach α ρ r f ≃ Bits k :=
  (physicalBuild (roleIndex R hR) r f).trans
    (Layout.permFn (normIndex ((stick X r f).cat (Layout.std a)) hk) F)

theorem shape_cat_code {δ ε : Type*} [Fintype δ] [Fintype ε]
    (D : Layout δ) (E : Layout ε) (v : Space (δ ⊕ ε)) :
    (shape (D.cat E)).loc v =
      (shape D).loc (fun j => v (.inl j)) +
      2^D.n * (shape E).loc (fun j => v (.inr j)) := by
  unfold shape
  rw [Layout.digits_code,Layout.digits_code,Layout.digits_code,
    Fintype.sum_sum_type]
  change (∑ j : δ, (v (.inl j)).val * 2^(D.loc j)) +
      (∑ j : ε, (v (.inr j)).val * 2^(D.n+E.loc j)) =
    (∑ j : δ, (v (.inl j)).val * 2^(D.loc j)) +
      2^D.n * (∑ j : ε, (v (.inr j)).val * 2^(E.loc j))
  simp_rw [pow_add]
  rw [mul_sum]
  congr 1
  apply sum_congr rfl
  intro j hj
  ring

theorem physical_code (X : Layout α) (R : Layout ρ) (a r f k : Nat)
    (hR : R.n=2^a) (hk : X.n*f+r+a=k) (q : Beach α ρ r f) :
    (bits k).loc (physicalSerial X R a r f k hR hk q)=
      (fleet X R r f).loc q := by
  unfold physicalSerial
  simp only [Equiv.trans_apply]
  rw [normal_code,shape_cat_code]
  change (shape (stick X r f)).loc (build α r f q.2)+
    2^(X.n*f+r)*(bits a).loc (roleIndex R hR q.1)=_
  rw [book_code,roleIndex_code]
  change _ = R.loc q.1*(book X r f).n+(book X r f).loc q.2
  rw [book_len]
  ring

theorem physical_size (X : Layout α) (R : Layout ρ) (a r f k : Nat)
    (hR : R.n=2^a) (hk : X.n*f+r+a=k) : (fleet X R r f).n=2^k := by
  change R.n*(book X r f).n=_
  rw [hR,book_len,← pow_add]
  congr 1; omega

theorem physical_tape (X : Layout α) (R : Layout ρ) (a r f k : Nat)
    (hR : R.n=2^a) (hk : X.n*f+r+a=k) (v : Bits k → ℂ) :
    (fleet X R r f).tape (fun q => v (physicalSerial X R a r f k hR hk q))=
      (bits k).tape v := by
  let e := physicalSerial X R a r f k hR hk
  refine Layout.verify (bits k) _ 0 _ ?_ ?_
  · exact physical_size X R a r f k hR hk
  · intro j
    obtain ⟨q,rfl⟩ := e.surjective j
    rw [physical_code]
    exact Layout.read _ _ q _

theorem kernel_physical (X : Layout α) (R : Layout ρ) (a r f k : Nat)
    (hR : R.n=2^a) (hk : X.n*f+r+a=k) (q z : Beach α ρ r f) :
    kernel (Fin k) (physicalSerial X R a r f k hR hk q)
      (physicalSerial X R a r f k hR hk z) =
    kernel (Fin a) (roleIndex R hR q.1) (roleIndex R hR z.1) *
      kernel (Fin r) q.2.1 z.2.1 *
      digitProd (fun _ : Fin f => kernel α) q.2.2 z.2.2 := by
  unfold physicalSerial
  simp only [Equiv.trans_apply]
  rw [kernel_permute]
  change (∏ j : Layers α r f ⊕ Fin a,
    littleC (physicalBuild (roleIndex R hR) r f q j)
      (physicalBuild (roleIndex R hR) r f z j))=_
  rw [Fintype.prod_sum_type]
  change kernel (Layers α r f) (build α r f q.2) (build α r f z.2) *
    kernel (Fin a) (roleIndex R hR q.1) (roleIndex R hR z.1)=_
  rw [kernel_build]
  ring

def remnant (r f : Nat) (v : Grain α ρ r f) : Grain α ρ r f :=
  fun q => chords r f (fun z => v (q.1,z)) q.2

theorem full_kernel (X : Layout α) (R : Layout ρ) (a r f k : Nat)
    (hR : R.n=2^a) (hk : X.n*f+r+a=k)
    (A : ρ → OBase α)
    (P : OriginalGroupedFrameWords.Word α ρ)
    (hp : ∀ x, OriginalGroupedFrameWords.walk A f P x=
      multiAct f (fun _ => kernel α) x) (v : Bits k → ℂ)
    (q : Beach α ρ r f) :
    let e := physicalSerial X R a r f k hR hk
    roleKernelPoint (roleIndex R hR)
      (OriginalGroupedWordRAM.coastline A r f P (remnant r f (fun q => v (e q)))) q =
      ripple k v (e q) := by
  intro e
  unfold roleKernelPoint OriginalGroupedWordRAM.coastline
  simp_rw [hp]
  change (∑ l, kernel (Fin a) _ _ *
    ∑ j, digitProd (fun _ : Fin f => kernel α) q.2.2 j *
      ∑ t, kernel (Fin r) q.2.1 t * v (e (l,t,j))) =
    ∑ z, kernel (Fin k) (e q) z * v z
  rw [← Equiv.sum_comp e]
  simp_rw [Fintype.sum_prod_type]
  have HK (z : Beach α ρ r f) : kernel (Fin k) (e q) (e z) =
      kernel (Fin a) (roleIndex R hR q.1) (roleIndex R hR z.1) *
      kernel (Fin r) q.2.1 z.2.1 *
      digitProd (fun _ : Fin f => kernel α) q.2.2 z.2.2 :=
    kernel_physical X R a r f k hR hk q z
  simp_rw [HK]
  simp only [mul_sum]
  apply sum_congr rfl
  intro l hl
  rw [sum_comm]
  apply sum_congr rfl
  intro t ht
  apply sum_congr rfl
  intro j hj
  ring

end
end FourierSchur.OriginalGroupedPhysicalBits
