import work_in_progress.OriginalGroupedCensusBridge
import work_in_progress.OriginalGroupedBodyInstantiationRAM
import work_in_progress.OriginalGroupedNativeProfile
import work_in_progress.OriginalSharedBlockCompletion

/-! The exact native residual census, attached to its own complete framed
word, now supplies a closed arbitrary-input RAM executor.  The geometric
moment is not assumed: CensusBridge derives it from that same emitted word.
The bound remains a power saving; no polylogarithmic bound is asserted. -/
namespace FourierSchur.OriginalGroupedCensusExecutor
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty
open OAI.PowerSaving.Selection OAI.PowerSaving.Skies OAI.PowerSaving.Slant
open OriginalSectorSubstitution OriginalCompilerRootBridge
noncomputable section

abbrev exponent : ℝ := OriginalGroupedResidualCertificate.alpha32

theorem exponent_pos : 0<exponent :=
  OriginalGroupedResidualCertificate.exponents_pos_lt.2.2.1

theorem exponent_lt : exponent<1 :=
  OriginalGroupedResidualCertificate.exponents_pos_lt.2.2.2

def profile (n : ℕ) : ℕ := ⌈((n:ℝ)+1)^exponent⌉₊

theorem profile_monotone : Monotone profile := by
  intro k l hkl
  apply Nat.ceil_mono
  apply Real.rpow_le_rpow (by positivity) _ exponent_pos.le
  exact_mod_cast Nat.add_le_add_right hkl 1

theorem profile_bound (k : ℕ) :
    (profile k:ℝ)+1≤3*((k:ℝ)+2)^exponent := by
  have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg
    (by positivity : 0≤(k:ℝ)+1) exponent)
  have hm : ((k:ℝ)+1)^exponent≤((k:ℝ)+2)^exponent :=
    Real.rpow_le_rpow (by positivity) (by linarith) exponent_pos.le
  have hbase : (1:ℝ)≤(k:ℝ)+2 := by
    have hk := Nat.cast_nonneg (α:=ℝ) k
    linarith
  have h1 : 1≤((k:ℝ)+2)^exponent := Real.one_le_rpow hbase exponent_pos.le
  unfold profile
  linarith

theorem allowance_bound
    (p : OriginalGroupedFrameWords.Word Cluster.Blocks Cluster.Role)
    (hm : OriginalGroupedWordProfile.moment p Cluster.mcol 50 exponent<1) :
    ∃ c : ℕ, ∀ k : ℕ,
      OriginalGroupedRecursionRAM.allowance
        (OriginalGroupedWordProfile.scheme p 50 (by decide)) k+1≤
      c*(2^k*profile k+1) := by
  have hm' : OriginalGroupedWordProfile.moment p
      (Fintype.card Cluster.Blocks) 50 exponent<1 := by
    simpa only [Cluster.card_block] using hm
  obtain ⟨C,hC,h⟩ := OriginalGroupedNativeProfile.word_allowance_bound p 50
    (by decide) (by norm_num [Cluster.card_block,Cluster.mcol])
    exponent exponent_pos.le hm'
  obtain ⟨c,hc⟩ := exists_nat_ge C
  have ht : 1≤c := Nat.one_le_cast.mp (hC.trans hc)
  refine ⟨c,fun k => ?_⟩
  have hg : (OriginalGroupedRecursionRAM.allowance
      (OriginalGroupedWordProfile.scheme p 50 (by decide)) k:ℝ)≤
      c*((2:ℝ)^k*(profile k:ℝ)) := by
    have hh : ((k:ℝ)+1)^exponent≤(profile k:ℝ) := Nat.le_ceil _
    apply (h k).trans
    rw [← mul_assoc]
    gcongr
  have he : OriginalGroupedRecursionRAM.allowance
      (OriginalGroupedWordProfile.scheme p 50 (by decide)) k≤
      c*(2^k*profile k) := by
    exact_mod_cast hg
  rw [mul_add,mul_one]
  omega

/-- The same complete native word whose exact census is proved in
CensusBridge.  Every original independent bank and all grouped RAM charges
are retained, including terminal full-order calls. -/
theorem grouped_census_program (cl : Paint) (m : Bool)
    {ι : Type} (k : ι→ℕ) (v : ∀ i, Bits (k i)→ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i))
      (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*profile (k i)) := by
  obtain ⟨P,hM,hsem⟩ := OriginalGroupedCensusBridge.native_word_alpha32
  let X := Layout.someLayout Cluster.Blocks
  let R := Layout.someLayout Cluster.Role
  have hR : R.n=2^50 := R.card.symm.trans Cluster.card_role
  have hX : X.n=Cluster.mcol := X.card.symm.trans Cluster.card_block
  have H := OriginalGroupedBodyInstantiationRAM.grouped_program cl m X R 50
    (by decide) hR (by rw [hX]; norm_num [Cluster.mcol])
    Cluster.bases P hsem k v
  obtain ⟨c,hc⟩ := allowance_bound P hM
  exact H.weaken ⟨c,fun i => hc (k i)⟩

theorem complete_executor (cl : Paint) (m : Bool) :
    CompleteTensorExecutor cl m profile :=
  grouped_census_program cl m
    (fun i : TensorInput => i.1) (fun i => i.2)

/-- One program for every positive Fourier length and arbitrary complex
input, with the actual profile-dependent all-length compiler bill. -/
theorem executeOne_census :
    ∃ (program : Prog false dftInKind dftOutKind) (d C p : ℕ),
      ∀ (n : ℕ), 0<n → ∀ x : Vec n,
      (run program (n,root (receipt n),(⟨n,x⟩:Tape ℂ))).OK
        (⟨n,dft n x⟩:Tape ℂ)
        (C*(OriginalAllLengthSubstitution.fairwind profile d n+1)) ((n+2)^p) := by
  exact OriginalAllLengthSubstitution.executeOne_supplied
    (OriginalSharedBlockCompletion.supplied_of_complete
      (complete_executor .left false) sc parentRoot)
    (OriginalSharedBlockCompletion.supplied_of_complete
      (complete_executor .scalar false) sc parentRoot)
    profile_monotone

end
end FourierSchur.OriginalGroupedCensusExecutor
