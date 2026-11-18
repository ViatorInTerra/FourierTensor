import work_in_progress.OriginalGroupedWordRAM
import work_in_progress.OriginalGroupedResidualRAM

/-! Paid embedding of a complete raw residual bank into the live role array.
All roles remain arbitrary independent inputs. Each raw input is gathered,
the open residual program is executed, and every coordinate is scattered
back. External child work is retained with coefficient one. -/
namespace FourierSchur.OriginalGroupedRoleResidualRAM
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty Matrix Finset
open scoped BigOperators
noncomputable section

universe U
variable {α ρ : Type*} [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ] {ι : Type U}
variable {m : Bool} {f : ι → Nat} {s : Ty} {x : ι → T s}
  {cl : Paint} {X : Layout α} {R : Layout ρ} {r : Nat}
  {v : ∀ i, Grain α ρ r (f i)}

def replaceRole {r f : Nat} (l : ρ) (v : Grain α ρ r f) (w : Grid α r f → ℂ) :
    Grain α ρ r f := fun q => if q.1=l then w q.2 else v q

/-- A full scalar/address gather of the selected physical role. -/
theorem gather_role {B : ι → Nat} (h : Rig m B f s x cl X R r v) (l : ρ) :
    Can m B s (simIn cl) x
      (fun i => GroupedResidual.givenGrid cl X r (f i) (fun a => v i (l,a)))
      (fun i => (fleet X R r (f i)).n) := by
  have hle (i) : (book X r (f i)).n ≤ (fleet X R r (f i)).n := by
    change _ ≤ R.n * _
    exact Nat.le_mul_of_pos_left _ (by have H := R.bd l; omega)
  have HA : Can m B s (bundle cl) x
      (fun i => (book X r (f i)).tape (fun a => v i (l,a)))
      (fun i => (book X r (f i)).n) := by
    have H := Can.layout (t:=c cl) (P:=fun _ => 0)
      (L:=fun i => book X r (f i)) (v:=fun i a => v i (l,a))
      (h.gear.grid_size X r) ?_ (h.gear.grid_small X r)
    · simpa only [Nat.zero_add,Nat.mul_zero,Nat.add_zero] using H
    · let S := Σ i, Grid α r (f i)
      let env (d : S) : T (p s w) := (x d.1,(book X r (f d.1)).loc d.2)
      have hg := h.gather (fun d : S => d.1) env (t:=p s w) Can.first
      exact hg.read (fun d => (l,d.2)) (Can.wc (R.loc l)) Can.second
  exact (h.gear.given.mono (fun _ => Nat.zero_le _)).pair
    ((h.imag.mono (fun _ => Nat.zero_le _)).pair (HA.mono hle))

/-- Actual role-bank assembly around a paid open raw residual program. The
program keeps the source environment and replaces only this role's data. -/
theorem embed_open (b : Bank (hatch cl) ι)
    (h : Rig m b.B f s x cl X R r v) (l : ρ)
    (w : ∀ i, Grid α r (f i) → ℂ) (Z : ι → Nat)
    (Hraw : Able m b (simIn cl) (bundle cl)
      (fun i => GroupedResidual.givenGrid cl X r (f i) (fun a => v i (l,a)))
      (fun i => (book X r (f i)).tape (w i))
      (fun i => (book X r (f i)).n) Z) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (replaceRole l (v i) (w i)))
      (fun i => (fleet X R r (f i)).n) Z := by
  let raw i := GroupedResidual.givenGrid cl X r (f i) (fun a => v i (l,a))
  let env1 i : T (p s (simIn cl)) := (x i,raw i)
  let env2 i : T (p (p s (simIn cl)) (bundle cl)) :=
    (env1 i,(book X r (f i)).tape (w i))
  have hle (i) : (book X r (f i)).n ≤ (fleet X R r (f i)).n := by
    change _ ≤ R.n * _
    exact Nat.le_mul_of_pos_left _ (by have H := R.bd l; omega)
  have HA := Able.of_can (b:=b) (gather_role h l)
  have HR : Able m b (p s (simIn cl)) (bundle cl) env1
      (fun i => (book X r (f i)).tape (w i))
      (fun i => (fleet X R r (f i)).n) Z := by
    simpa only [Nat.zero_add] using
      (Able.of_can (b:=b) (Can.second (W:=fun i => (fleet X R r (f i)).n))).comp_keep
        (Hraw.mono hle (fun _ => le_rfl))
  have hg := h.gather id env2 (t:=p (p s (simIn cl)) (bundle cl))
    (Can.fst Can.first)
  have HC : Can m b.B (p (p s (simIn cl)) (bundle cl)) (bundle cl) env2
      (fun i => (fleet X R r (f i)).tape (replaceRole l (v i) (w i)))
      (fun i => (fleet X R r (f i)).n) := by
    refine hg.chart _ ?_
    let S := Σ i, Beach α ρ r (f i)
    let env3 (d : S) : T (p (p (p s (simIn cl)) (bundle cl)) Ty.w) :=
      (env2 d.1,(fleet X R r (f d.1)).loc d.2)
    have hh := hg.gather (fun d : S => d.1) env3 Can.first
    obtain ⟨hl,hk⟩ := hh.addrs (fun d => d.2) Can.second
    have old := hh.read (fun d => d.2) hl hk
    have fresh : Has m (fun d : S => b.B d.1) _ (c cl) env3
        (fun d => w d.1 d.2.2) :=
      Can.fetch (t:=c cl) (L:=fun d : S => book X r (f d.1))
        (v:=fun d => w d.1) (i:=fun d => d.2.2)
        (Can.snd Can.first) hk
    apply Can.cases_code (q:=fun d : S => d.2.1) R hl
    intro a
    by_cases ha : a=l
    · refine (fresh.reindex (fun d : {d : S // d.2.1=a} => d.1)).cong
        (fun _ => rfl) (fun d => ?_)
      simp [replaceRole,d.2,ha]
    · refine (old.reindex (fun d : {d : S // d.2.1=a} => d.1)).cong
        (fun _ => rfl) (fun d => ?_)
      simp [replaceRole,d.2,ha]
  have HT := HA.save_keep (HR.save_keep (Able.of_can (b:=b) HC))
  simpa only [Nat.zero_add,Nat.add_zero] using HT

def partialRoles {r f : Nat} (op : ρ → (Grid α r f → ℂ) → Grid α r f → ℂ)
    (P : Finset ρ) (v : Grain α ρ r f) : Grain α ρ r f :=
  fun q => if q.1 ∈ P then op q.1 (fun a => v (q.1,a)) q.2 else v q

theorem partialRoles_insert {r f : Nat}
    (op : ρ → (Grid α r f → ℂ) → Grid α r f → ℂ)
    (P : Finset ρ) (l : ρ) (hl : l ∉ P) (v : Grain α ρ r f) :
    replaceRole l (partialRoles op P v)
      (op l (fun a => partialRoles op P v (l,a))) =
    partialRoles op (insert l P) v := by
  funext q
  by_cases hq : q.1=l
  · simp [replaceRole,partialRoles,hq,hl]
  · simp [replaceRole,partialRoles,hq]

/-- Uniform paid per-role service, rather than a matrix-action oracle. -/
def RoleService (b : Bank (hatch cl) ι)
    (op : ∀ f : Nat, ρ → (Grid α r f → ℂ) → Grid α r f → ℂ)
    (Z : ρ → ι → Nat) : Prop :=
  ∀ (s : Ty) (x : ι → T s) (v : ∀ i, Grain α ρ r (f i))
    (h : Rig m b.B f s x cl X R r v) (l : ρ),
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape
        (replaceRole l (v i) (op (f i) l (fun a => v i (l,a)))))
      (fun i => (fleet X R r (f i)).n) (Z l)

/-- Finite static role dispatch and full gathers/scatters compose into one
native open program. Different child orders retain their own additive charge. -/
theorem all_roles (b : Bank (hatch cl) ι)
    (op : ∀ f : Nat, ρ → (Grid α r f → ℂ) → Grid α r f → ℂ)
    (Z : ρ → ι → Nat)
    (HS : RoleService (m:=m) (f:=f) (X:=X) (R:=R) (r:=r) b op Z)
    (h : Rig m b.B f s x cl X R r v) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape
        (fun q => op (f i) q.1 (fun a => v i (q.1,a)) q.2))
      (fun i => (fleet X R r (f i)).n) (fun i => ∑ l, Z l i) := by
  have HP (P : Finset ρ) :
      Able m b s (bundle cl) x
        (fun i => (fleet X R r (f i)).tape
          (partialRoles (op (f i)) P (v i)))
        (fun i => (fleet X R r (f i)).n) (fun i => ∑ l ∈ P, Z l i) := by
    induction P using Finset.induction with
    | empty =>
      simpa [partialRoles] using Able.of_can (b:=b)
        (h.items.mono (W':=fun i => (fleet X R r (f i)).n) (fun _ => Nat.zero_le _))
    | insert l P hl ih =>
      let v' i := partialRoles (op (f i)) P (v i)
      let env i : T (p s (bundle cl)) := (x i,(fleet X R r (f i)).tape (v' i))
      have hg := h.gather id env (t:=p s (bundle cl)) Can.first
      have next : Rig m b.B f (p s (bundle cl)) env cl X R r v' :=
        ⟨hg.gear,hg.imag,Can.second⟩
      have H := ih.save_keep (HS _ env v' next l)
      have He (i) : replaceRole l (v' i)
          (op (f i) l (fun a => v' i (l,a))) =
          partialRoles (op (f i)) (insert l P) (v i) :=
        partialRoles_insert _ P l hl (v i)
      simpa only [He,Finset.sum_insert hl,Nat.add_comm] using H
  have He (i) : partialRoles (op (f i)) univ (v i) =
      (fun q => op (f i) q.1 (fun a => v i (q.1,a)) q.2) := by
    funext q; simp [partialRoles]
  simpa only [He] using HP univ

end
end FourierSchur.OriginalGroupedRoleResidualRAM
