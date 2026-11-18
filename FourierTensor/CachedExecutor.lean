import FourierTensor.Tensor.CenterCache.Word
import FourierTensor.Tensor.CenterCache.Assembly
import FourierTensor.Tensor.CenterCache.Charge
import FourierTensor.Tensor.Workspace
import FourierTensor.Tensor.ExponentComparison

/-! The revised invocation, its complete global word, and a uniform native
executor compiled at the exponent certified by that word's own census. -/
namespace FourierTensor.CachedExecutor

open FourierSchur OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.Cluster
open OAI.PowerSaving.RAM OriginalSectorSubstitution OriginalCertifiedTensorBackend
open OriginalGroupedFrameWords OriginalGroupedCensusBridge OriginalGroupedWordProfile
open OriginalNativeCenterSharing CenterCacheAssembly
noncomputable section
set_option maxRecDepth 8192

abbrev exponent := CenterCacheRate.exponent
abbrev density := WorkspaceExecutor.density

theorem exponent_eq : exponent = 1 - 3 / 100000000 := rfl

theorem saving_ratio :
    142420.49 < (1-exponent)/(1-theta) ∧ (1-exponent)/(1-theta) < 142420.50 :=
  ExponentComparison.saving_ratio

private theorem local_words : LocalWords CenterCacheCensus.invocationCost :=
  fun j F rev => CenterCacheWord.invocation j F rev

/-- At every stage, in either orientation, the output-correct local word
has exactly 63 instruction/row pairs of rank 32. -/
theorem local_rank32 (j : J) (F : StartAxes) (rev : Bool) :
    ∃ p : Word Blocks (Box ⊕ Free),
      (Finset.univ.filter (fun q : Kind p => rank p q = 32)).card = 63 ∧
      ∀ f x, OriginalGroupedFrameWords.walk (CenterCacheWord.basis j F) f p
          (withFrame (CenterCacheWord.basis j F) (CenterCacheWord.labels (bp j)) f x) =
        withFrame (CenterCacheWord.basis j F) (CenterCacheWord.labels (bend j)) f
          (point f (CenterCacheWord.applyOriginal (if rev then OriginalGroupedPricedSharedNetwork.backward
            else OriginalGroupedPricedSharedNetwork.forward)) x) := by
  obtain ⟨p,hp,hs⟩ := CenterCacheWord.invocation j F rev
  refine ⟨p,?_,hs⟩
  let c (r : ℕ) : ℝ := if r=32 then 1 else 0
  have hc : c 0=0 := rfl
  have ht := hp c hc
  have hj : CenterCacheCensus.invocationCost j c = 63 := CenterCacheCensus.rank32_invocation j
  rw [wordCost_eq p c hc,hj] at ht
  simp [c] at ht
  exact_mod_cast ht

private theorem exists_word :
    ∃ p : Word Blocks BankRole,
      (∀ c : ℕ → ℝ, c 0=0 → wordCost p c=CenterCacheCensus.nativeCost c) ∧
      ∀ f (x : Data Blocks BankRole f) (r : Role),
        OriginalGroupedFrameWords.walk bankBasis f p x (.inl r) =
          matAct f (kernel Blocks) (x (.inl r)) :=
  CenterCacheAssembly.complete_word local_words

def word : Word Blocks BankRole := Classical.choose exists_word

theorem word_cost (c : ℕ → ℝ) (hc : c 0=0) :
    wordCost word c=CenterCacheCensus.nativeCost c :=
  (Classical.choose_spec exists_word).1 c hc

theorem all_outputs : WorkspaceExecutor.OriginalOutputs bankBasis word :=
  fun f x r => (Classical.choose_spec exists_word).2 f (Sum.elim x (fun _ => 0)) r

/-- Exact number of rank-32 entries across the three stages, read off the
same global word supplied to the native compiler. -/
theorem global_rank32 :
    (Finset.univ.filter (fun q : Kind word => rank word q = 32)).card = 3115400400 := by
  exact CenterCacheCensus.word_rank_count word word_cost (3 : Fin 12)

theorem word_moment : moment word mcol 50 exponent < 1 :=
  CenterCacheCensus.word_moment_lt word word_cost

theorem complete_executor (cl : Paint) (mode : Bool) : CompleteTensorExecutor cl mode density :=
  WorkspaceExecutor.complete_of_word bankBasis word all_outputs word_moment cl mode

abbrev Certificate (cl : Paint) (mode : Bool) := RawCertifiedFor density cl mode

def backend (cl : Paint) (mode : Bool) : Certificate cl mode :=
  Classical.choice (rawCertified_of_complete (complete_executor cl mode))

/-- A fixed program returns all dense complex coordinates at every order.
The bill includes scalar preparation, movement and a polynomial word cap. -/
theorem guarantee (cl : Paint) (mode : Bool) (n : ℕ) (input : Fin (2^n) → ℂ) :
    (run (backend cl mode).program (rawInput cl n input)).OK
      (⟨2^n, tensorAction n fourierKernel input⟩ : OAI.PowerSaving.Tape ℂ)
      ((backend cl mode).costConstant * (2^n * density n + 1))
      ((2^n + 2)^(backend cl mode).wordDegree) :=
  (backend cl mode).guarantee n input

end
end FourierTensor.CachedExecutor

namespace FourierTensor.CachedExecutor

open FourierSchur.OriginalGroupedRecursionRAM FourierSchur.OriginalGroupedWordProfile

/-- The physical child price of this particular word equals the charge
specified by the twelve-rank histogram, for any prices on child orders. -/
theorem child_charge (k : ℕ) (τ : ℕ → ℕ) :
    childCharge (scheme word 50 (by decide)) k τ = childCharge CenterCacheRate.scheme k τ :=
  CenterCacheCharge.childCharge_eq word word_cost k τ

/-- Equality holds at every order of the recursively defined allowance. -/
theorem charged_allowance (k : ℕ) :
    allowance (scheme word 50 (by decide)) k = allowance CenterCacheRate.scheme k :=
  CenterCacheCharge.allowance_eq word word_cost k

open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.Cluster
open FourierSchur FourierSchur.OriginalGroupedFrameWords FourierSchur.OriginalNativeCenterSharing

/-- At amplification `f`, every one of the 63 rank-32 requests runs on all
its independent spectator arrays. The same invocation supplies every output. -/
theorem local_physical_rank32 (j : J) (F : StartAxes) (rev : Bool) :
    ∃ p : Word Blocks (Box ⊕ Free),
      (∀ (X : Layout Blocks) (r f : ℕ), 0 < f →
        OriginalGroupedWordRAM.wordCharge X r f (fun k => if k = 32*f then 1 else 0) p =
          63 * 2^(r + (X.n - 32)*f)) ∧
      ∀ f x, OriginalGroupedFrameWords.walk (CenterCacheWord.basis j F) f p
          (withFrame (CenterCacheWord.basis j F) (CenterCacheWord.labels (bp j)) f x) =
        withFrame (CenterCacheWord.basis j F) (CenterCacheWord.labels (bend j)) f
          (point f (CenterCacheWord.applyOriginal (if rev then OriginalGroupedPricedSharedNetwork.backward
            else OriginalGroupedPricedSharedNetwork.forward)) x) := by
  obtain ⟨p, hp, hs⟩ := local_rank32 j F rev
  refine ⟨p, ?_, hs⟩
  intro X r f hf
  rw [CenterCacheCharge.physical_count p X r f 32 hf (by decide), hp]

end FourierTensor.CachedExecutor
