import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! A coefficient-independent finite chunk-size selector using the exact
two-convolution gate count. Three displacement branches execute serially
and reuse the restored scratch bank. No unknown asymptotic constant enters
the capacity test. -/
namespace FourierSchur.ToeplitzChunkSize

def capacity (k : Nat) : Nat := (16*k+50)*2^k

def eligible (v : Nat) : Finset Nat :=
  (Finset.range (v+1)).filter (fun k => capacity k ≤ v)

theorem capacity_width (k : Nat) : 2^k ≤ capacity k := by
  unfold capacity
  calc
    2^k=1*2^k := by omega
    _ ≤ (16*k+50)*2^k := Nat.mul_le_mul_right _ (by omega)

theorem capacity_order (v k : Nat) (h : capacity k ≤ v) : k < v :=
  lt_of_lt_of_le Nat.lt_two_pow_self ((capacity_width k).trans h)

theorem eligible_nonempty (v : Nat) (hv : 50 ≤ v) : (eligible v).Nonempty := by
  refine ⟨0,?_⟩
  simp only [eligible,Finset.mem_filter,Finset.mem_range,capacity,mul_zero,zero_add,pow_zero,mul_one]
  exact ⟨by omega,hv⟩

def selected (v : Nat) (hv : 50 ≤ v) : Nat := (eligible v).max' (eligible_nonempty v hv)

theorem selected_mem (v : Nat) (hv : 50 ≤ v) : selected v hv∈eligible v :=
  Finset.max'_mem _ _

theorem selected_capacity (v : Nat) (hv : 50 ≤ v) : capacity (selected v hv) ≤ v :=
  (Finset.mem_filter.mp (selected_mem v hv)).2

theorem selected_maximal (v : Nat) (hv : 50 ≤ v) (k : Nat) (hk : capacity k ≤ v) :
    k ≤ selected v hv := by
  apply Finset.le_max'
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
    have h := capacity_order v k hk
    omega),hk⟩

theorem selected_successor (v : Nat) (hv : 50 ≤ v) : v < capacity (selected v hv+1) := by
  by_contra h
  have hs := selected_maximal v hv (selected v hv+1) (by omega)
  omega

theorem selected_log_bound (v : Nat) (hv : 50 ≤ v) : selected v hv ≤ Nat.log 2 v :=
  Nat.le_log_of_pow_le (by decide)
    ((capacity_width _).trans (selected_capacity v hv))

theorem selected_width_positive (v : Nat) (hv : 50 ≤ v) : 0 < 2^(selected v hv) := by positivity

theorem successor_capacity (k : Nat) : capacity (k+1)=(32*k+132)*2^k := by
  simp only [capacity,pow_succ]
  ring

theorem selected_cover (v : Nat) (hv : 50 ≤ v) :
    v < (32*selected v hv+132)*2^(selected v hv) := by
  simpa only [successor_capacity] using selected_successor v hv

def chunkCount (n b : Nat) : Nat := (n+b-1)/b

theorem chunkCount_bound (v n : Nat) (hv : 50 ≤ v) (hn : n ≤ v) :
    chunkCount n (2^(selected v hv)) ≤ 32*selected v hv+132 := by
  have hb := selected_width_positive v hv
  have hc := selected_cover v hv
  unfold chunkCount
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hb).mpr
  rw [Nat.succ_mul]
  omega

theorem chunkPairCount_bound (v n m : Nat) (hv : 50 ≤ v) (hn : n ≤ v) (hm : m ≤ v) :
    chunkCount n (2^(selected v hv))*chunkCount m (2^(selected v hv)) ≤
      (32*selected v hv+132)^2 := by
  simpa only [pow_two] using Nat.mul_le_mul (chunkCount_bound v n hv hn) (chunkCount_bound v m hv hm)

theorem fft_width (k : Nat) : 2^(k+2)=4*2^k := by
  rw [pow_add]
  norm_num
  omega

theorem chunk_fft_fits (k a e : Nat) (ha : a ≤ 2^k) (he : e ≤ 2^k) :
    2*(e+a) ≤ 2^(k+2) := by
  rw [fft_width]
  omega

theorem chunk_workspace_fits (v a e : Nat) (hv : 50 ≤ v)
    (ha : a ≤ 2^(selected v hv)) (he : e ≤ 2^(selected v hv)) :
    e+a+(4*(selected v hv+2)+4)*2^(selected v hv+2) ≤ v := by
  have hc := selected_capacity v hv
  rw [fft_width]
  unfold capacity at hc
  nlinarith

theorem chunk_root_bound (v : Nat) (hv : 50 ≤ v) : 2^(selected v hv+2) ≤ 4*v := by
  rw [fft_width]
  exact Nat.mul_le_mul_left 4 ((capacity_width _).trans (selected_capacity v hv))

def nodeRoundBudget (v : Nat) (hv : 50 ≤ v) : Nat :=
  3*(32*selected v hv+132)^2*(80*selected v hv+250)

theorem nodeRoundBudget_bound (v : Nat) (hv : 50 ≤ v) :
    nodeRoundBudget v hv ≤ 13068000*(Nat.log 2 v+1)^3 := by
  have hk := selected_log_bound v hv
  have hc : 32*selected v hv+132 ≤ 132*(Nat.log 2 v+1) := by omega
  have hd : 80*selected v hv+250 ≤ 250*(Nat.log 2 v+1) := by omega
  unfold nodeRoundBudget
  calc
    _ ≤ 3*(132*(Nat.log 2 v+1))^2*(250*(Nat.log 2 v+1)) := by gcongr
    _ = 13068000*(Nat.log 2 v+1)^3 := by ring

theorem chunkSerialRounds_bound (v n m : Nat) (hv : 50 ≤ v) (hn : n ≤ v) (hm : m ≤ v) :
    3*(chunkCount n (2^(selected v hv))*chunkCount m (2^(selected v hv)))*
      (80*(selected v hv+2)+90) ≤ 13068000*(Nat.log 2 v+1)^3 := by
  calc
    _ ≤ nodeRoundBudget v hv := by
      unfold nodeRoundBudget
      have hp := chunkPairCount_bound v n m hv hn hm
      have he : 80*(selected v hv+2)+90=80*selected v hv+250 := by omega
      rw [he]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 3 hp)
    _ ≤ _ := nodeRoundBudget_bound v hv

end FourierSchur.ToeplitzChunkSize
