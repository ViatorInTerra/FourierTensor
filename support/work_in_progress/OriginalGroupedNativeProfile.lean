import work_in_progress.OriginalGroupedWordProfile
import work_in_progress.OriginalGroupedAllowanceBound

/-! Connect the emitted native grouped word to its charged allowance.
This conservative profile is established from the actual word's first
moment. It does not import an unconnected edge histogram as a cost claim. -/
namespace FourierSchur.OriginalGroupedNativeProfile
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OriginalGroupedWordProfile OriginalGroupedRecursionRAM
open scoped BigOperators
noncomputable section

theorem word_allowance_bound {α : Type*} {ρ : Type} [Fintype α] [DecidableEq α]
    [Fintype ρ] [DecidableEq ρ] (p : OriginalGroupedFrameWords.Word α ρ)
    (a : ℕ) (ha : 0 < a) (hu : 0 < Fintype.card α) (z : ℝ) (hz : 0 ≤ z)
    (hm : moment p (Fintype.card α) a z < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ k : ℕ,
      (allowance (scheme p a ha) k : ℝ) ≤ C*(2:ℝ)^k*((k:ℝ)+1)^z := by
  have hzero (q : Kind p) (hq : rank p q=0) : weight p q=0 := by
    simp [weight,hq]
  exact OriginalGroupedAllowanceBound.grouped_allowance_bound
    (Fintype.card α) a (a+Fintype.card α) (rank p) (weight p)
    hu ha (Nat.le_add_right _ _) le_rfl (rank_le p) hzero z hz hm

theorem hills_allowance (p : OriginalGroupedFrameWords.Word Cluster.Blocks Cluster.Role)
    (hm : moment p Cluster.mcol 50 alpha < 1) :
    ∃ c : ℕ, ∀ k : ℕ,
      allowance (scheme p 50 (by decide)) k+1 ≤ c*(2^k*hills k+1) := by
  have hm' : moment p (Fintype.card Cluster.Blocks) 50 alpha < 1 := by
    simpa only [Cluster.card_block] using hm
  obtain ⟨C,hC,h⟩ := word_allowance_bound p 50 (by decide)
    (by norm_num [Cluster.card_block,Cluster.mcol]) alpha alpha_pos.le hm'
  obtain ⟨c,hc⟩ := exists_nat_ge C
  have ht : 1 ≤ c := Nat.one_le_cast.mp (hC.trans hc)
  refine ⟨c,fun k => ?_⟩
  have hg : (allowance (scheme p 50 (by decide)) k:ℝ) ≤
      c*((2:ℝ)^k*(hills k:ℝ)) := by
    have hh : ((k:ℝ)+1)^alpha ≤ (hills k:ℝ) := Nat.le_ceil _
    apply (h k).trans
    rw [← mul_assoc]
    gcongr
  have he : allowance (scheme p 50 (by decide)) k ≤ c*(2^k*hills k) := by
    exact_mod_cast hg
  rw [mul_add,mul_one]
  omega

/-- One actual finite grouped word has both exact all-role semantics and
a proved native allowance envelope. The closed program is supplied by
the separately compiled RAM body, not inferred from these matrices. -/
theorem native_word_with_allowance :
    ∃ p : OriginalGroupedFrameWords.Word Cluster.Blocks Cluster.Role,
      (∀ f (x : Data Cluster.Blocks Cluster.Role f),
        OriginalGroupedFrameWords.walk Cluster.bases f p x =
          multiAct f (fun _ => kernel Cluster.Blocks) x) ∧
      ∃ c : ℕ, ∀ k : ℕ,
        allowance (scheme p 50 (by decide)) k+1 ≤ c*(2^k*hills k+1) := by
  obtain ⟨p,hp,hm,he⟩ := native_word
  exact ⟨p,he,hills_allowance p hm⟩

end
end FourierSchur.OriginalGroupedNativeProfile
