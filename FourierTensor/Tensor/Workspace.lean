import FourierTensor.Tensor.CenterCache.Rate
import work_in_progress.OriginalScratchGroupedInstantiationRAM
import work_in_progress.OriginalGroupedNativeProfile
import work_in_progress.OriginalCertifiedTensorBackend

/-!
# Grouped RAM programs with temporary banks

The input and output layouts contain just the independent original banks.
A fixed finite set of extra banks may hold data during a grouped word.
Allocation, clearing, and extraction are pointwise native operations.
The recursive bill counts each positive-rank instruction on either kind
of bank, with the denominator determined by the input layout.
-/

namespace FourierTensor.WorkspaceExecutor
open FourierSchur OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty Matrix Finset
open FourierSchur.OriginalGroupedWordRAM FourierSchur.OriginalGroupedFrameWords
open FourierSchur.OriginalLocalizedBankWorkspaceRAM FourierSchur.OriginalLocalizedBankSharing
open FourierSchur.OriginalGroupedPhysicalBits FourierSchur.OriginalGroupedRoleBitsRAM
open FourierSchur.OriginalScratchGroupedBodyRAM FourierSchur.OriginalGroupedRecursionRAM
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000

variable {α η κ : Type} [Fintype α] [DecidableEq α]
  [Fintype η] [DecidableEq η] [Fintype κ] [DecidableEq κ]

/-- The program observes every original bank with fresh zero workspace. -/
def OriginalOutputs (A : (η ⊕ κ) → OBase α) (P : Word α (η ⊕ κ)) : Prop :=
  ∀ (f : ℕ) (x : Data α η f) (i : η),
    walk A f P (Sum.elim x (fun _ => 0)) (.inl i) = matAct f (kernel α) (x i)

private def clearWorkspace (P : Word α (η ⊕ κ)) : Word α (η ⊕ κ) :=
  P ++ [.localM (gatherMatrix (0 : Matrix κ η ℚ))]

private theorem cleared_output {A : (η ⊕ κ) → OBase α} {P : Word α (η ⊕ κ)}
    (h : OriginalOutputs A P) {r f : ℕ} (v : Grain α η r f) :
    coastline A r f (clearWorkspace P) (padded v) = padded (κ := κ) (kernelGrain v) := by
  funext q
  rcases q with ⟨role, s, z⟩
  let x : Data α η f := fun j t => v (j, s, t)
  have hx : (fun (l : η ⊕ κ) t => padded v (l, s, t)) =
      Sum.elim x (fun _ => 0) := by
    funext l t
    cases l <;> rfl
  unfold OriginalGroupedWordRAM.coastline clearWorkspace
  rw [hx, OriginalGroupedFrameWords.walk_append]
  cases role with
  | inl i =>
    change actPoint (gatherMatrix (0 : Matrix κ η ℚ)) _ (.inl i) = _
    rw [gather_original]
    exact congrFun (h f x i) z
  | inr i =>
    change actPoint (gatherMatrix (0 : Matrix κ η ℚ)) _ (.inr i) = 0
    simp [gather_scratch]

omit [Fintype α] [DecidableEq κ] in
private theorem cleared_charge (P : Word α (η ⊕ κ)) (X : Layout α)
    (r f : ℕ) (τ : ℕ → ℕ) :
    wordCharge X r f τ (clearWorkspace P) = wordCharge X r f τ P := by
  simp [clearWorkspace, wordCharge, moveCharge]

universe U
variable {ι : Type U}

private theorem run_workspace {m : Bool} {f : ι → ℕ} {s : Ty} {x : ι → T s}
    {cl : Paint} {X : Layout α} {R0 : Layout η} {r : ℕ}
    {v : ∀ i, Grain α η r (f i)}
    (b : Bank (hatch cl) ι) (h : Rig m b.B f s x cl X R0 r v)
    (R : Layout (η ⊕ κ)) (j : η) (hr : 3 ≤ X.n)
    (A : (η ⊕ κ) → OBase α) (tau : ι → ℕ → ℕ)
    (HC : ∀ n : ℕ, 0 < n → n ≤ X.n → GroupedResidual.Rig.RawContract cl b
      (fun i => n * f i) (fun i => tau i (n * f i)))
    (P : Word α (η ⊕ κ)) (H : OriginalOutputs A P) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R0 r (f i)).tape (kernelGrain (v i)))
      (fun i => (fleet X R0 r (f i)).n)
      (fun i => wordCharge X r (f i) (tau i) P) := by
  let env i : T (Ty.p s (bundle cl)) :=
    (x i, (fleet X R r (f i)).tape (padded (κ := κ) (v i)))
  have hg := h.gather id env (t := Ty.p s (bundle cl)) Can.first
  have hp : Rig m b.B f (Ty.p s (bundle cl)) env cl X R r
      (fun i => padded (κ := κ) (v i)) := ⟨hg.gear, hg.imag, Can.second⟩
  have hf := OriginalGroupedFrameCompilerRAM.frame_service cl m X R r hr f A b tau HC
  have hs := sweep A b tau hf hp (clearWorkspace P)
  have hn := (Able.of_can (b := b) (prepare_scratch h R)).save_keep hs
  have hw : Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (padded (κ := κ) (kernelGrain (v i))))
      (fun i => (fleet X R0 r (f i)).n)
      (fun i => wordCharge X r (f i) (tau i) P) := by
    simp only [Nat.zero_add, cleared_charge, cleared_output H] at hn
    apply hn.weaken ?_ (fun _ => Nat.le_refl _)
    refine ⟨R.n + 1, fun i => ?_⟩
    have hw := workspace_width (X := X) (R0 := R0) (r := r) R j (f i)
    dsimp
    nlinarith
  let out i : T (Ty.p s (bundle cl)) :=
    (x i, (fleet X R r (f i)).tape (padded (κ := κ) (kernelGrain (v i))))
  have hy := h.gather id out (t := Ty.p s (bundle cl)) Can.first
  have hq : Rig m b.B f (Ty.p s (bundle cl)) out cl X R r
      (fun i => padded (κ := κ) (kernelGrain (v i))) := ⟨hy.gear, hy.imag, Can.second⟩
  have he := extract_original (R0 := R0) hq
  simpa only [Nat.add_zero] using hw.save_keep (Able.of_can (b := b) he)

private theorem physical_body (cl : Paint) (m : Bool)
    (X : Layout α) (R0 : Layout η) (R : Layout (η⊕κ)) (j : η) (a r : ℕ)
    (hR : R0.n=2^a) (hr : 3≤X.n) (hd : r<X.n)
    (b : Bank (hatch cl) ι) (k f : ι→ℕ)
    (hk : ∀ i,X.n*f i+r+a=k i) (v : ∀ i,Bits (k i)→ℂ)
    (hB : Small b.B (fun i => 2^k i))
    (A : (η⊕κ)→OBase α) (tau : ι→ℕ→ℕ)
    (HC : ∀ n : ℕ,0<n → n≤X.n → GroupedResidual.Rig.RawContract cl b
      (fun i => n*f i) (fun i => tau i (n*f i)))
    (P : Word α (η ⊕ κ)) (H : OriginalOutputs A P) :
    Able m b (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i))
      (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i)
      (fun i => wordCharge X r (f i) (tau i) P) := by
  let W i := 2^k i
  let env i := givenBits cl (k i) (v i)
  let e i := physicalSerial X R0 a r (f i) (k i) hR (hk i)
  let inp i : Grain α η r (f i) := fun q => v i (e i q)
  let z i := remnant r (f i) (inp i)
  have hsize (i) : (fleet X R0 r (f i)).n=W i :=
    physical_size X R0 a r (f i) (k i) hR (hk i)
  have hf (i) : f i≤k i := by
    have H := Nat.le_mul_of_pos_left (f i) (show 0<X.n by omega)
    have K := hk i
    omega
  have hlen (i) : k i≤W i := Nat.lt_two_pow_self.le
  have sq := (hB.mono hlen).mono hf
  have hm : Small b.B (fun i => 2^f i) :=
    hB.mono (fun i => Nat.pow_le_pow_right (by omega) (hf i))
  have hcube (i) : (2^f i)^3≤W i := by
    dsimp [W]
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by omega)
    have H := Nat.mul_le_mul_right (f i) hr
    have K := hk i
    omega
  have HG : Can m b.B (simIn cl) Ty.w env f W := by
    have HT : Can m b.B (simIn cl) Ty.w env k W := Can.first
    refine ((HT.minus (Can.wc a) (hB.mono hlen)).dvdW
      (Can.wc X.n) ((hB.mono hlen).sub)).cong (fun _ => rfl) ?_
    intro i
    rw [← hk i,Nat.add_sub_cancel,mul_comm X.n]
    exact Layout.div_join hd
  have HP : Can m b.B (simIn cl) (p Ty.w Ty.w) env
      (fun i => (f i,2^f i)) W :=
    HG.pair (HG.wTwo sq hm (Dom.of_le (fun i => (hf i).trans (hlen i))))
  let T1 := p (simIn cl) (p Ty.w Ty.w)
  let env1 i : Ty.T T1 := (env i,f i,2^f i)
  have HX : Can m b.B T1 (Ty.a Ty.w) env1 (fun i => xorTab (f i)) W :=
    (Can.xor_prepare (m:=m) (f:=f) (B:=b.B) (s:=T1) (x:=env1)
      (Can.fst Can.second) (Can.snd Can.second) sq hm).mono hcube
  let T2 := p T1 (Ty.a Ty.w)
  let env2 i : Ty.T T2 := (env1 i,xorTab (f i))
  have HI : Rig m b.B f T2 env2 cl X R0 r inp := by
    have H : Has m b.B T2 (simIn cl) env2 env := Can.fst Can.first
    refine ⟨⟨Can.snd (Can.snd Can.first),Can.fst (Can.snd Can.first),Can.second,hm⟩,
      H.snd.fst,?_⟩
    exact H.snd.snd.cong (fun _ => rfl)
      (fun i => (physical_tape X R0 a r (f i) (k i) hR (hk i) (v i)).symm)
  have HD : Can m b.B T2 (bundle cl) env2
      (fun i => (fleet X R0 r (f i)).tape (z i)) W := by
    simpa only [hsize] using HI.dots_cost
  let T3 := p T2 (bundle cl)
  let env3 i : Ty.T T3 := (env2 i,(fleet X R0 r (f i)).tape (z i))
  have hz := HI.gather id env3 (t:=T3) Can.first
  have HZ : Rig m b.B f T3 env3 cl X R0 r z := ⟨hz.gear,hz.imag,Can.second⟩
  have HW := (run_workspace b HZ R j hr A tau HC P H).mono
    (fun i => (hsize i).le) (fun _ => le_rfl)
  let y i := kernelGrain (z i)
  let T4 := p T3 (bundle cl)
  let env4 i : Ty.T T4 := (env3 i,(fleet X R0 r (f i)).tape (y i))
  have hy := HZ.gather id env4 (t:=T4) Can.first
  have HY : Rig m b.B f T4 env4 cl X R0 r y := ⟨hy.gear,hy.imag,Can.second⟩
  have HA := roleKernel_cost HY (roleIndex R0 hR)
  have HE (i) : (fleet X R0 r (f i)).tape (roleKernelPoint (roleIndex R0 hR) (y i))=
      (bits (k i)).tape (ripple (k i) (v i)) := by
    have hfun : roleKernelPoint (roleIndex R0 hR) (y i)=
        (fun q => ripple (k i) (v i) (e i q)) := by
      funext q
      exact complete_physical X R0 a r (f i) (k i) hR (hk i) (v i) q
    rw [hfun]
    exact physical_tape X R0 a r (f i) (k i) hR (hk i) _
  have HO := (Able.of_can (b:=b) (HA.mono (fun i => (hsize i).le))).cong
    (fun _ => rfl) HE
  have HT := (Able.of_can (b:=b) HP).save_keep
    ((Able.of_can (b:=b) HX).save_keep ((Able.of_can (b:=b) HD).save_keep
      (HW.save_keep HO)))
  simpa only [Nat.zero_add,Nat.add_zero,hsize] using HT

private theorem open_body (cl : Paint) (m : Bool)
    (X : Layout α) (R0 : Layout η) (R : Layout (η⊕κ)) (j : η)
    (a : ℕ) (ha : 0<a) (hR : R0.n=2^a) (hu : 3≤X.n)
    (A : (η⊕κ)→OBase α) (P : Word α (η ⊕ κ)) (Hsem : OriginalOutputs A P) :
    OpenBody (OriginalGroupedWordProfile.scheme P a ha) cl m := by
  let Y := OriginalGroupedRecursionRAM.Desc cl
  let B := OriginalGroupedRecursionRAM.funds cl
  let K := a+X.n
  let env (i : Y) := givenBits cl i.k i.v
  have HX : Can m B.B (simIn cl) Ty.w env (fun i => i.k) B.B := Can.first
  change Able m B (simIn cl) (bundle cl) env
    (fun i => (bits i.k).tape (ripple i.k i.v)) B.B
    (OriginalGroupedRecursionRAM.charge (OriginalGroupedWordProfile.scheme P a ha))
  apply Able.branch (HX.wlt (Can.wc K)) (fun i => K ≤ i.k)
    (fun i => by split <;> omega)
  · let G := {i : Y // K ≤ i.k}
    let rem (i : G) := (i.1.k-a)%X.n
    have hrem (i : G) : rem i<X.n := Nat.mod_lt _ (by omega)
    have hw : Small (fun i : G => B.B i.1) rem :=
      (Small.const _ X.n).mono (fun i => (hrem i).le)
    have HM : Can m (fun i : G => B.B i.1) (simIn cl) Ty.w
        (fun i => env i.1) rem (fun i => B.B i.1) :=
      (((HX.reindex (fun i : G => i.1)).minus (Can.wc a)
        ((Small.self B.B).reindex (fun i : G => i.1) |>.mono
          (fun i => Nat.lt_two_pow_self.le))).wmod (Can.wc X.n) hw)
    apply Able.dispatch (n:=rem) X.n HM hrem
    intro r hr
    let L := {i : G // rem i=r}
    let l (i : L) : Y := i.1.1
    let Q := B.comap l
    let k (i : L) := (l i).k
    let f (i : L) := (k i-a)/X.n
    let tau (i : L) := (l i).tau
    have hbig (i : L) : a+X.n≤k i := i.1.2
    have hk (i : L) : X.n*f i+r+a=k i := by
      have H : X.n*f i+(k i-a)%X.n=k i-a := by
        simpa only [f,Nat.mul_comm] using Nat.div_add_mod (k i-a) X.n
      have Hr : (k i-a)%X.n=r := i.2
      rw [Hr] at H
      have Hb := hbig i
      omega
    have hf (i : L) : 0<f i := by
      apply Nat.div_pos (by have H := hbig i; omega) (by omega)
    have HC (n : ℕ) (hn : 0<n) (hnle : n≤X.n) :
        GroupedResidual.Rig.RawContract cl Q (fun i => n*f i)
          (fun i => tau i (n*f i)) := by
      intro i w
      have Hn := Nat.mul_le_mul_right (f i) hnle
      have Hk := hk i
      have Hord : n*f i<(l i).k := by
        change n*f i<k i
        omega
      exact (l i).works (n*f i) Hord w
    have H := physical_body cl m X R0 R j a r hR hu hr Q k f hk
      (fun i => (l i).v) (Small.self _) A tau HC P Hsem
    apply H.mono (fun _ => le_rfl)
    intro i
    change wordCharge X r (f i) (tau i) P ≤
      childCharge (OriginalGroupedWordProfile.scheme P a ha) (k i) (tau i)
    rw [OriginalGroupedWordProfile.charge_eq_wordCharge P a ha X r (f i) (k i)
      hr (by have Hk := hk i; omega) (hf i)]
  · let L := {i : Y // ¬(K ≤ i.k)}
    have hsmall (i : L) : i.1.k<K := Nat.lt_of_not_ge i.2
    apply Able.dispatch K (HX.reindex (fun i : L => i.1)) hsmall
    intro j hj
    let T0 := {i : L // i.1.k=j}
    let l (i : T0) : Y := i.1.1
    let Q := B.comap l
    let k (i : T0) := (l i).k
    have hk (i : T0) : k i=j := i.2
    have H := hills_program cl m k (fun i => (l i).v)
    have HD : Dom (fun i => 2^k i) (fun i => 2^k i*hills (k i)) := by
      refine ⟨hills j+1,fun i => ?_⟩
      change 2^k i*hills (k i)+1≤(hills j+1)*(2^k i+1)
      rw [hk i]
      nlinarith [Nat.one_le_pow j 2 (by omega)]
    exact (Able.of_can (b:=Q) (H.weaken HD)).mono
      (fun _ => le_rfl) (fun _ => Nat.zero_le _)

theorem grouped_program (cl : Paint) (m : Bool)
    (X : Layout α) (R0 : Layout η) (R : Layout (η⊕κ)) (j : η)
    (a : ℕ) (ha : 0<a) (hR : R0.n=2^a) (hu : 3≤X.n)
    (A : (η⊕κ)→OBase α) (P : Word α (η ⊕ κ)) (Hsem : OriginalOutputs A P)
    {ι : Type} (k : ι→ℕ) (v : ∀ i,Bits (k i)→ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i))
      (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => allowance (OriginalGroupedWordProfile.scheme P a ha) (k i)) :=
  close_grouped_body _ cl m (open_body cl m X R0 R j a ha hR hu A P Hsem) k v

def density (k : ℕ) : ℕ := ⌈((k : ℝ) + 1) ^ CenterCacheRate.exponent⌉₊

theorem allowance_bound (P : Word Cluster.Blocks (Cluster.Role ⊕ κ))
    (hm : OriginalGroupedWordProfile.moment P Cluster.mcol 50 CenterCacheRate.exponent < 1) :
    ∃ c : ℕ, ∀ k : ℕ, allowance (OriginalGroupedWordProfile.scheme P 50 (by decide)) k + 1 ≤
      c * (2 ^ k * density k + 1) := by
  obtain ⟨C, hC, h⟩ := OriginalGroupedNativeProfile.word_allowance_bound P 50
    (by decide) (by norm_num [Cluster.card_block, Cluster.mcol])
    CenterCacheRate.exponent CenterCacheRate.exponents_pos_lt.1.le (by
      simpa only [Cluster.card_block] using hm)
  obtain ⟨c, hc⟩ := exists_nat_ge C
  have ht : 1 ≤ c := Nat.one_le_cast.mp (hC.trans hc)
  refine ⟨c, fun k => ?_⟩
  have hg : (allowance (OriginalGroupedWordProfile.scheme P 50 (by decide)) k : ℝ) ≤
      c * ((2 : ℝ)^k * (density k : ℝ)) := by
    have hh : ((k : ℝ) + 1) ^ CenterCacheRate.exponent ≤ (density k : ℝ) := Nat.le_ceil _
    apply (h k).trans
    rw [← mul_assoc]
    gcongr
  have he : allowance (OriginalGroupedWordProfile.scheme P 50 (by decide)) k ≤
      c * (2 ^ k * density k) := by exact_mod_cast hg
  rw [mul_add, mul_one]
  omega

open OriginalSectorSubstitution OriginalCertifiedTensorBackend

/-- With an all-output augmented word and a moment computed from that word,
the native compiler produces one bounded program for every tensor order. -/
theorem complete_of_word (A : (Cluster.Role ⊕ κ) → OBase Cluster.Blocks)
    (P : Word Cluster.Blocks (Cluster.Role ⊕ κ)) (h : OriginalOutputs A P)
    (hm : OriginalGroupedWordProfile.moment P Cluster.mcol 50 CenterCacheRate.exponent < 1)
    (cl : Paint) (m : Bool) : CompleteTensorExecutor cl m density := by
  let X := Layout.someLayout Cluster.Blocks
  let R := Layout.someLayout Cluster.Role
  have hR : R.n = 2 ^ 50 := R.card.symm.trans Cluster.card_role
  have hX : X.n = Cluster.mcol := X.card.symm.trans Cluster.card_block
  have hr : Nonempty Cluster.Role :=
    Fintype.card_pos_iff.mp (by rw [Cluster.card_role]; unfold Cluster.tower; positivity)
  have hc := grouped_program cl m X R (Layout.someLayout (Cluster.Role ⊕ κ))
    (Classical.choice hr) 50 (by decide) hR (by rw [hX]; norm_num [Cluster.mcol])
    A P h (fun i : TensorInput => i.1) (fun i => i.2)
  obtain ⟨c, hcost⟩ := allowance_bound P hm
  exact hc.weaken ⟨c, fun i => hcost i.1⟩

theorem dense_of_word (A : (Cluster.Role ⊕ κ) → OBase Cluster.Blocks)
    (P : Word Cluster.Blocks (Cluster.Role ⊕ κ)) (h : OriginalOutputs A P)
    (hm : OriginalGroupedWordProfile.moment P Cluster.mcol 50 CenterCacheRate.exponent < 1)
    (cl : Paint) (m : Bool) : Nonempty (RawCertifiedFor density cl m) :=
  rawCertified_of_complete (complete_of_word A P h hm cl m)


end
end FourierTensor.WorkspaceExecutor
