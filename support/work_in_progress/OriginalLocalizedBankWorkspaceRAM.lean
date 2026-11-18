import work_in_progress.OriginalNativeCenterSharing

/-! Paid scratch creation around the local sharing word. The caller supplies
only original role data. Fresh scratch is explicitly initialized by a native
tabulation; it is not an additional arbitrary input or a free workspace. -/
namespace FourierSchur.OriginalLocalizedBankWorkspaceRAM
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty Matrix Finset
open OriginalGroupedWordRAM OriginalLocalizedBankSharing
noncomputable section
universe U
variable {α η κ : Type*} [Fintype α] [DecidableEq α]
  [Fintype η] [DecidableEq η] [Fintype κ] [DecidableEq κ]
  {ι : Type U} {m : Bool} {cl : Paint} {f : ι → ℕ}
  {s : Ty} {x : ι → T s} {X : Layout α} {R0 : Layout η} {r : ℕ}
  {v : ∀ i, Grain α η r (f i)}

def padded {r f : ℕ} (v : Grain α η r f) (q : Beach α (η ⊕ κ) r f) : ℂ :=
  match q.1 with
  | .inl j => v (j,q.2)
  | .inr _ => 0

omit [Fintype α] [DecidableEq α] [Fintype η] [DecidableEq η]
  [Fintype κ] [DecidableEq κ] in
theorem workspace_width (R : Layout (η ⊕ κ)) (j : η) (fi : ℕ) :
    (fleet X R r fi).n≤R.n*(fleet X R0 r fi).n := by
  change R.n*(book X r fi).n≤R.n*(R0.n*(book X r fi).n)
  apply Nat.mul_le_mul_left
  exact Nat.le_mul_of_pos_left _ (by have H := R0.bd j; omega)

omit [Fintype α] [DecidableEq α] in
theorem prepare_scratch {B : ι → ℕ}
    (h : Rig m B f s x cl X R0 r v) (R : Layout (η ⊕ κ)) :
    Can m B s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (padded (κ:=κ) (v i)))
      (fun i => (fleet X R r (f i)).n) := by
  have Hsize : Knows m B s x (fun i => (fleet X R r (f i)).n) :=
    (Can.wc R.n).times (h.gear.grid_size X r)
      (Small.const B R.n) (h.gear.grid_small X r)
  have Hsmall : Small B (fun i => (fleet X R r (f i)).n) :=
    (Small.const B R.n).mul (h.gear.grid_small X r)
  have H := Can.layout (t:=c cl) (P:=fun _ => 0)
    (L:=fun i => fleet X R r (f i)) (v:=fun i => padded (κ:=κ) (v i))
    Hsize ?_ Hsmall
  · simpa only [Nat.zero_add,Nat.mul_zero,Nat.add_zero] using H
  · let Q := Σ i, Beach α (η ⊕ κ) r (f i)
    let env (d : Q) : T (p s w) := (x d.1,(fleet X R r (f d.1)).loc d.2)
    have hg := h.gather (fun d : Q => d.1) env (t:=p s w) Can.first
    have hs := Hsmall.reindex (fun d : Q => d.1)
    have hl : Knows m (fun d : Q => B d.1) (p s w) env
        (fun d => R.loc d.2.1) :=
      Can.addr_high (u:=fun d : Q => d.2) (L:=fun _ => R)
        (R:=fun d : Q => book X r (f d.1)) Can.second
        (hg.gear.grid_size X r) hs
    have hk : Knows m (fun d : Q => B d.1) (p s w) env
        (fun d => (book X r (f d.1)).loc d.2.2) :=
      Can.addr_low (u:=fun d : Q => d.2) (L:=fun _ => R)
        (R:=fun d : Q => book X r (f d.1)) Can.second
        (hg.gear.grid_size X r) hs
    apply Can.cases_code (q:=fun d : Q => d.2.1) R hl
    intro role
    cases role with
    | inl j =>
      have HR := hg.read (fun d : Q => (j,d.2.2)) (Can.wc (R0.loc j)) hk
      refine (HR.reindex (fun d : {d : Q // d.2.1=Sum.inl j} => d.1)).cong
        (fun _ => rfl) (fun d => ?_)
      simp [padded,d.2]
    | inr k =>
      apply Can.zero.cong (fun _ => rfl)
      intro d
      simp [padded,d.2]

/-- Complete local open program starting with ORIGINAL roles only. The
augmented output retains the original roles plus cleared scratch slots;
that workspace can be reused by subsequent local words. Allocation and
every zero store are charged by prepare_scratch. -/
theorem fresh_sharedRatioWord_native (b : Bank (hatch cl) ι)
    (h : Rig m b.B f s x cl X R0 r v) (R : Layout (η ⊕ κ))
    (hr : 3≤X.n) (A : (η ⊕ κ) → OBase α) (tau : ι → ℕ → ℕ)
    (HC : ∀ n : ℕ, 0<n → n≤X.n → GroupedResidual.Rig.RawContract cl b
      (fun i => n*f i) (fun i => tau i (n*f i)))
    (B : Matrix κ η ℚ) (D : Matrix η κ ℚ) (S T : Finset α) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape
        (coastline A r (f i) (sharedRatioWord B D S T) (padded (v i))))
      (fun i => (fleet X R r (f i)).n)
      (fun i => Fintype.card κ * (if ((S\T) ∪ (T\S)).card=0 then 0 else
        (2^r*(2^f i)^(X.n-((S\T) ∪ (T\S)).card))*tau i (((S\T) ∪ (T\S)).card*f i))) := by
  let env i : Ty.T (p s (bundle cl)) :=
    (x i,(fleet X R r (f i)).tape (padded (κ:=κ) (v i)))
  have hg := h.gather id env (t:=p s (bundle cl)) Can.first
  have hp : Rig m b.B f (p s (bundle cl)) env cl X R r
      (fun i => padded (κ:=κ) (v i)) := ⟨hg.gear,hg.imag,Can.second⟩
  have HS := sharedRatioWord_native b hp hr A tau HC B D S T
  have H := (Able.of_can (b:=b) (prepare_scratch h R)).save_keep HS
  simpa only [Nat.zero_add] using H

/-- The complete initialized local routine has linear nonrecursive work
in the ORIGINAL input width. Weakening changes only the local constant;
every child callback retains coefficient one in the price. -/
theorem fresh_sharedRatioWord_original_cost (b : Bank (hatch cl) ι)
    (h : Rig m b.B f s x cl X R0 r v) (R : Layout (η ⊕ κ)) (j : η)
    (hr : 3≤X.n) (A : (η ⊕ κ) → OBase α) (tau : ι → ℕ → ℕ)
    (HC : ∀ n : ℕ, 0<n → n≤X.n → GroupedResidual.Rig.RawContract cl b
      (fun i => n*f i) (fun i => tau i (n*f i)))
    (B : Matrix κ η ℚ) (D : Matrix η κ ℚ) (S T : Finset α) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape
        (coastline A r (f i) (sharedRatioWord B D S T) (padded (v i))))
      (fun i => (fleet X R0 r (f i)).n)
      (fun i => Fintype.card κ * (if ((S\T) ∪ (T\S)).card=0 then 0 else
        (2^r*(2^f i)^(X.n-((S\T) ∪ (T\S)).card))*tau i (((S\T) ∪ (T\S)).card*f i))) := by
  have H := fresh_sharedRatioWord_native b h R hr A tau HC B D S T
  apply H.weaken ?_ (fun _ => Nat.le_refl _)
  refine ⟨R.n+1,fun i => ?_⟩
  have hw := workspace_width (X:=X) (R0:=R0) (r:=r) R j (f i)
  dsimp
  nlinarith

end
end FourierSchur.OriginalLocalizedBankWorkspaceRAM
