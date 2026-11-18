import work_in_progress.OriginalGroupedRoleResidualRAM

/-! The fixed role index is part of the physical tensor, not an auxiliary
replicated copy. This paid point pass applies its remaining fixed `a` kernel
axes after the grouped word has acted on every residual bank. -/
namespace FourierSchur.OriginalGroupedRoleBitsRAM
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty Matrix Finset
open scoped BigOperators
noncomputable section

def roleIndex {ρ : Type*} (R : Layout ρ) {a : Nat} (hR : R.n=2^a) :
    ρ ≃ Bits a := R.index.trans ((finCongr hR).trans (bits a).index.symm)

theorem roleIndex_code {ρ : Type*} (R : Layout ρ) {a : Nat} (hR : R.n=2^a)
    (l : ρ) : (bits a).loc (roleIndex R hR l)=R.loc l := by
  have h := (bits a).loc_atFin ((finCongr hR) (R.toIx l))
  exact h

def roleKernelPoint {α ρ : Type*} [Fintype ρ] {a r f : Nat}
    (e : ρ ≃ Bits a) (v : Grain α ρ r f) : Grain α ρ r f :=
  fun q => ∑ j, kernel (Fin a) (e q.1) (e j) * v (j,q.2)

universe U
variable {α ρ : Type*} [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ] {ι : Type U}
variable {m : Bool} {B f : ι → Nat} {s : Ty} {x : ι → T s}
  {cl : Paint} {X : Layout α} {R : Layout ρ} {r a : Nat}
  {v : ∀ i, Grain α ρ r (f i)}

/-- All fixed coefficients are built from the native paid `littleC` operations;
each data coefficient is loaded and each output is stored by actual RAM loops. -/
theorem roleKernel_read (h : Rig m B f s x cl X R r v) (e : ρ ≃ Bits a)
    (q : ∀ i, Beach α ρ r (f i))
    (g : Knows m B s x fun i => (fleet X R r (f i)).loc (q i)) :
    Has m B s (c cl) x fun i => roleKernelPoint e (v i) (q i) := by
  obtain ⟨hl,hk⟩ := h.addrs q g
  change Can m B s (c cl) x
    (fun i => ∑ j, kernel (Fin a) (e (q i).1) (e j) * v i (j,(q i).2)) _
  apply Can.sum_cconst
  intro j
  have he : Has m B s sc x (fun i => kernel (Fin a) (e (q i).1) (e j)) := by
    apply Can.cases_code (q:=fun i => (q i).1) R hl
    intro l
    have Hc : Has m B s sc x (fun _ => kernel (Fin a) (e l) (e j)) :=
      Can.prod_cconst (v:=fun i _ => littleC (e l i) (e j i))
        (fun _ => h.little _ _)
    refine (Hc.reindex
      (fun i : {i // (q i).1=l} => i.1)).cong (fun _ => rfl) ?_
    intro i
    rw [i.2]
  exact he.mul (h.read (fun i => (j,(q i).2)) (Can.wc (R.loc j)) hk)

theorem roleKernel_cost (h : Rig m B f s x cl X R r v) (e : ρ ≃ Bits a) :
    Can m B s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (roleKernelPoint e (v i)))
      (fun i => (fleet X R r (f i)).n) := by
  refine h.chart _ ?_
  let S := Σ i, Beach α ρ r (f i)
  have hg := h.gather (fun d : S => d.1)
    (fun d => ((x d.1,(fleet X R r (f d.1)).loc d.2) : Ty.T (p s w)))
    (t:=p s w) Can.first
  exact roleKernel_read hg e (fun d => d.2) Can.second

end
end FourierSchur.OriginalGroupedRoleBitsRAM
