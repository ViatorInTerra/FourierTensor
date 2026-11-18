import work_in_progress.OriginalPhysicalChirpRAM

/-! Paid affine changes of physical coordinates. The fixed binary matrix
acts in every column. Word XOR uses the actual table already prepared by
the native Rig. No f-column scan is performed for each data coordinate. -/
namespace FourierSchur.OriginalPhysicalAffineRAM
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty Matrix Finset
noncomputable section

section Semantics
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [DecidableEq ρ]

def affine (M : Matrix α α F) (z : Space α) (q : Space α) : Space α :=
  M.mulVec q+z

def affineData (l : ρ) (M : Matrix α α F) (z : Space α) (r f : ℕ)
    (v : Grain α ρ r f) : Grain α ρ r f :=
  fun q => if q.1=l then v (q.1,q.2.1,fun j => affine M z (q.2.2 j)) else v q

theorem affineData_off (l : ρ) (M : Matrix α α F) (z : Space α) (r f : ℕ)
    (v : Grain α ρ r f) (q : Beach α ρ r f) (hq : q.1≠l) :
    affineData l M z r f v q=v q := by simp [affineData,hq]

theorem affineData_inverse (l : ρ) (M N : Matrix α α F) (z w : Space α)
    (hinv : ∀ q, affine M z (affine N w q)=q) (r f : ℕ)
    (v : Grain α ρ r f) :
    affineData l N w r f (affineData l M z r f v)=v := by
  funext q
  by_cases hq : q.1=l
  · simp only [affineData,hq,ite_true]
    congr 1
    exact Prod.ext hq.symm (Prod.ext rfl (funext fun j => hinv (q.2.2 j)))
  · simp [affineData,hq]
end Semantics

section Compiler
universe U
variable {α ρ : Type*} [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ] {ι : Type U}
  {m : Bool} {B f : ι→ℕ} {s : Ty} {x : ι→T s}
  {cl : Paint} {X : Layout α} {R : Layout ρ} {r : ℕ}
  {v : ∀ i, Grain α ρ r (f i)}

private theorem row_sum_read (g : Gear m B f s x) (X : Layout α)
    (q : ∀ i, Sky α (f i))
    (hq : Knows m B s x (fun i => (bodyOrder X (f i)).loc (q i)))
    (S : Finset α) (c : α→F) :
    Knows m B s x (fun i => (bits (f i)).loc
      (fun j => ∑ a∈S,c a*q i j a)) := by
  induction S using Finset.induction with
  | empty =>
    apply (Can.wc 0).cong (fun _ => rfl)
    intro i
    simp [bits_loc]
  | insert a S ha ih =>
    rcases bit_cases (c a) with hc|hc
    · apply ih.cong (fun _ => rfl)
      intro i
      simp [Finset.sum_insert ha,hc]
    · have H := g.addr_xor
        (fun i => ((fun j => q i j a),(fun j => ∑ b∈S,c b*q i j b)))
        (g.body_get X q a hq) ih
      apply H.cong (fun _ => rfl)
      intro i
      congr 1
      funext j
      simp [Finset.sum_insert ha,hc]

theorem affine_grid_read (g : Gear m B f s x) (X : Layout α) (r : ℕ)
    (M : Matrix α α F) (z : Space α) (q : ∀ i, Grid α r (f i))
    (hq : Knows m B s x (fun i => (book X r (f i)).loc (q i))) :
    Knows m B s x (fun i => (book X r (f i)).loc
      ((q i).1,fun j => affine M z ((q i).2 j))) := by
  obtain ⟨hs,hb⟩ := g.grid_fetch X r hq
  apply g.grid_combine X r
    (v:=fun i => ((q i).1,fun j => affine M z ((q i).2 j))) hs
  apply g.body_set X
  intro a
  have H := row_sum_read g X (fun i => (q i).2) hb univ (M a)
  rcases bit_cases (z a) with hz|hz
  · apply H.cong (fun _ => rfl)
    intro i
    simp [affine,Matrix.mulVec, dotProduct,hz]
  · have hlit : Knows m B s x (fun i => (bits (f i)).loc (fun _ => (1:F))) :=
      (g.power.minus (Can.wc 1) g.bound).cong (fun _ => rfl) (fun i => by
        change 2^f i-1=(bits (f i)).loc (fun _ => 1)
        rw [← bits_lit]
        simp)
    have K := g.addr_xor
      (fun i => ((fun j => ∑ b : α,M a b*(q i).2 j b),(fun _ => (1:F)))) H hlit
    apply K.cong (fun _ => rfl)
    intro i
    congr 1
    funext j
    simp [affine,Matrix.mulVec,dotProduct,hz]

theorem affineData_read (h : Rig m B f s x cl X R r v)
    (l : ρ) (M : Matrix α α F) (z : Space α)
    (q : ∀ i, Beach α ρ r (f i))
    (hq : Knows m B s x (fun i => (fleet X R r (f i)).loc (q i))) :
    Has m B s (c cl) x (fun i => affineData l M z r (f i) (v i) (q i)) := by
  obtain ⟨hl,hb⟩ := h.addrs q hq
  let q' i : Beach α ρ r (f i) :=
    ((q i).1,(q i).2.1,fun j => affine M z ((q i).2.2 j))
  have H := h.read q' hl (affine_grid_read h.gear X r M z (fun i => (q i).2) hb)
  have K := h.read q hl hb
  apply Can.cases_code (q:=fun i => (q i).1) R hl
  intro role
  by_cases he : role=l
  · apply (H.reindex (fun i : {i // (q i).1=role} => i.val)).cong (fun _ => rfl)
    intro i
    simp [affineData,q',i.property,he]
  · apply (K.reindex (fun i : {i // (q i).1=role} => i.val)).cong (fun _ => rfl)
    intro i
    simp [affineData,i.property,he]

/-- Every physical read, output write and address computation is compiled.
The zero child bill does not mean zero local execution cost. -/
theorem affineData_native (h : Rig m B f s x cl X R r v)
    (l : ρ) (M : Matrix α α F) (z : Space α) :
    Can m B s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (affineData l M z r (f i) (v i)))
      (fun i => (fleet X R r (f i)).n) := by
  refine h.chart _ ?_
  let S := Σ i, Beach α ρ r (f i)
  let env (d : S) : T (p s w) := (x d.1,(fleet X R r (f d.1)).loc d.2)
  have hh := h.gather (fun d : S => d.1) env (t:=p s w) Can.first
  exact affineData_read hh l M z (fun d => d.2) Can.second
end Compiler
end
end FourierSchur.OriginalPhysicalAffineRAM
