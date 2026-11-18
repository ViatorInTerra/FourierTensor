import work_in_progress.OriginalGroupedFrameBudget
import work_in_progress.OriginalGroupedWordRAM
import work_in_progress.OriginalGroupedPricedSharedNetwork
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-! The recursive inventory of the actual retained grouped word. Each kind
is a token and a physical role. Zero-rank blocks make no callback; every
nonzero block includes all of its spectator copies. The profile is derived
from this inventory rather than attached as an independent assumption. -/
namespace FourierSchur.OriginalGroupedWordProfile

open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OriginalGroupedFrameWords OriginalGroupedFrameBudget
open scoped BigOperators
noncomputable section

variable {α : Type*} {ρ : Type} [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ]

def moveRank : OriginalGroupedFrameWords.Move α ρ → ρ → ℕ
  | .frames s t, l => OriginalGroupedWordRAM.residualRank s t l
  | _, _ => 0

def Kind (p : Word α ρ) := Fin p.length × ρ

instance (p : Word α ρ) : Fintype (Kind p) := inferInstanceAs (Fintype (Fin p.length × ρ))
instance (p : Word α ρ) : DecidableEq (Kind p) := inferInstanceAs (DecidableEq (Fin p.length × ρ))

def rank (p : Word α ρ) (q : Kind p) : ℕ := moveRank (p.get q.1) q.2
def weight (p : Word α ρ) (q : Kind p) : ℕ := if rank p q = 0 then 0 else 1

theorem residualRank_eq (s t : ρ → Finset α) (l : ρ) :
    OriginalGroupedWordRAM.residualRank s t l = changeSize (s l) (t l) := by
  unfold OriginalGroupedWordRAM.residualRank changeSize
  apply Finset.card_union_of_disjoint
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1

theorem moveMoment_eq (g : OriginalGroupedFrameWords.Move α ρ) :
    moveMoment g = ∑ l, moveRank g l := by
  cases g with
  | frames s t => simp [moveMoment,moveRank,residualRank_eq]
  | localM M => simp [moveMoment,moveRank]
  | translate z => simp [moveMoment,moveRank]

theorem rank_le (p : Word α ρ) (q : Kind p) : rank p q ≤ Fintype.card α := by
  unfold rank
  cases p.get q.1 with
  | frames s t => exact Finset.card_le_univ _
  | localM M => exact Nat.zero_le _
  | translate z => exact Nat.zero_le _

theorem rank_sum (p : Word α ρ) : ∑ q : Kind p, rank p q = firstMoment p := by
  change (∑ q : Fin p.length × ρ, moveRank (p.get q.1) q.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [← moveMoment_eq]
  rw [← Fin.sum_ofFn, List.ofFn_comp', List.ofFn_get]
  rfl

theorem weighted_rank (p : Word α ρ) (q : Kind p) :
    weight p q * rank p q = rank p q := by
  by_cases h : rank p q = 0 <;> simp [weight,h]

theorem weighted_rank_sum (p : Word α ρ) :
    ∑ q : Kind p, weight p q * rank p q = firstMoment p := by
  simp_rw [weighted_rank]
  exact rank_sum p

theorem power_le_rank (p : Word α ρ) (q : Kind p) (a : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1) :
    (weight p q : ℝ) * (rank p q : ℝ)^a ≤ rank p q := by
  by_cases h : rank p q = 0
  · simp [weight,h,Real.zero_rpow ha.ne']
  · have hh : (1 : ℝ) ≤ rank p q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
    simpa [weight,h] using Real.rpow_le_rpow_of_exponent_le hh ha1

def moment (p : Word α ρ) (u a : ℕ) (z : ℝ) : ℝ :=
  ∑ q : Kind p, (weight p q : ℝ)/(2:ℝ)^a * ((rank p q : ℝ)/(u:ℝ))^z

theorem moment_firstMoment (p : Word α ρ) (u a : ℕ) (hu : 0 < u)
    (z : ℝ) (hz : 0 < z) (hz1 : z ≤ 1) :
    moment p u a z ≤ (firstMoment p : ℝ)/((2:ℝ)^a*(u:ℝ)^z) := by
  have hu' : (0:ℝ) < u := by exact_mod_cast hu
  have hpow : (0:ℝ) < (2:ℝ)^a*(u:ℝ)^z := by positivity
  calc
    moment p u a z =
        (∑ q : Kind p, (weight p q : ℝ)*(rank p q : ℝ)^z) /
          ((2:ℝ)^a*(u:ℝ)^z) := by
      unfold moment
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro q _
      rw [Real.div_rpow (Nat.cast_nonneg _) hu'.le]
      ring
    _ ≤ (∑ q : Kind p, (rank p q : ℝ)) / ((2:ℝ)^a*(u:ℝ)^z) := by
      apply div_le_div_of_nonneg_right _ hpow.le
      exact Finset.sum_le_sum fun q _ => power_le_rank p q z hz hz1
    _ = _ := by rw [← Nat.cast_sum, rank_sum]

def scheme (p : Word α ρ) (a : ℕ) (ha : 0 < a) :
    OriginalGroupedRecursionRAM.Scheme (Kind p) :=
  OriginalGroupedRecursionRAM.groupedScheme (Fintype.card α) a (a+Fintype.card α)
    (rank p) (weight p) ha (Nat.le_add_right _ _) (rank_le p)

theorem moveCharge_eq (X : Layout α) (r f : ℕ) (tau : ℕ → ℕ)
    (g : OriginalGroupedFrameWords.Move α ρ) :
    OriginalGroupedWordRAM.moveCharge X r f tau g =
      ∑ l, if moveRank g l = 0 then 0 else
        2^(r+(X.n-moveRank g l)*f)*tau (moveRank g l*f) := by
  cases g with
  | localM M => simp [OriginalGroupedWordRAM.moveCharge,moveRank]
  | translate z => simp [OriginalGroupedWordRAM.moveCharge,moveRank]
  | frames s t =>
    simp only [OriginalGroupedWordRAM.moveCharge,OriginalGroupedWordRAM.frameCharge,moveRank]
    congr 1
    funext l
    rw [← pow_mul,pow_add,Nat.mul_comm f]

/-- The program's recursive charge is exactly its scheme charge, including
all spectator fibers, when the parent is split into role and physical bits. -/
theorem charge_eq_wordCharge (p : Word α ρ) (a : ℕ) (ha : 0 < a)
    (X : Layout α) (r f k : ℕ) (hr : r < X.n)
    (hk : k = a+X.n*f+r) (hf : 0 < f) (tau : ℕ → ℕ) :
    OriginalGroupedRecursionRAM.childCharge (scheme p a ha) k tau =
      OriginalGroupedWordRAM.wordCharge X r f tau p := by
  have hX : Fintype.card α = X.n := X.card
  have hcut : a+Fintype.card α ≤ k := by
    have hh := Nat.mul_le_mul_left X.n hf
    omega
  have hdiv : (k-a)/(Fintype.card α)=f := by
    rw [hk,hX]
    have hh : a+X.n*f+r-a=X.n*f+r := by omega
    rw [hh,Nat.mul_add_div (by omega : 0<X.n),Nat.div_eq_of_lt hr,Nat.add_zero]
  unfold OriginalGroupedRecursionRAM.childCharge scheme
  simp only [OriginalGroupedRecursionRAM.groupedScheme,hcut,if_true,hdiv]
  change (∑ q : Fin p.length × ρ,
    weight p q * 2^(k-a-rank p q*f)*tau (rank p q*f)) = _
  rw [Fintype.sum_prod_type]
  have hp : OriginalGroupedWordRAM.wordCharge X r f tau p =
      ∑ j : Fin p.length, OriginalGroupedWordRAM.moveCharge X r f tau (p.get j) := by
    symm
    rw [← Fin.sum_ofFn,List.ofFn_comp',List.ofFn_get]
    rfl
  rw [hp]
  apply Finset.sum_congr rfl
  intro j _
  rw [moveCharge_eq]
  apply Finset.sum_congr rfl
  intro l _
  change (if rank p (j,l)=0 then 0 else 1) * 2^(k-a-rank p (j,l)*f)*tau (rank p (j,l)*f) =
    if rank p (j,l)=0 then 0 else 2^(r+(X.n-rank p (j,l))*f)*tau (rank p (j,l)*f)
  by_cases hz : rank p (j,l)=0
  · simp [hz]
  · have hb : rank p (j,l) ≤ X.n := (rank_le p (j,l)).trans_eq hX
    have he : k-a-rank p (j,l)*f = r+(X.n-rank p (j,l))*f := by
      rw [Nat.sub_mul]
      have hh := Nat.mul_le_mul_right f hb
      omega
    simp only [hz,if_false,Nat.one_mul,he]

/-- The exact native grouped word, with its profile proved from its own
first moment. This uses the archived conservative exponent; the stronger
finite histogram requires a separate connection to this emitted word. -/
theorem native_word :
    ∃ p : Word Cluster.Blocks Cluster.Role,
      firstMoment p = Cluster.nMoves ∧
      moment p Cluster.mcol 50 alpha < 1 ∧
      ∀ f (x : Data Cluster.Blocks Cluster.Role f),
        OriginalGroupedFrameWords.walk Cluster.bases f p x =
          multiAct f (fun _ => kernel Cluster.Blocks) x := by
  obtain ⟨p,hp,he⟩ := OriginalGroupedPricedSharedNetwork.certificate
  refine ⟨p,hp,?_,he⟩
  have hb := moment_firstMoment p Cluster.mcol 50 (by norm_num [Cluster.mcol])
    alpha alpha_pos alpha_lt.le
  rw [hp] at hb
  apply hb.trans_lt
  have hu : (0:ℝ) < Cluster.mcol := by norm_num [Cluster.mcol]
  have hd : (0:ℝ) < (2:ℝ)^50*(Cluster.mcol:ℝ)^alpha := by positivity
  apply (div_lt_one hd).mpr
  have hh := network_rate
  have hq : (0:ℝ) < (2:ℝ)^50 := by positivity
  exact (div_lt_iff₀ hq).mp hh |>.trans_eq (by ring)

end
end FourierSchur.OriginalGroupedWordProfile
