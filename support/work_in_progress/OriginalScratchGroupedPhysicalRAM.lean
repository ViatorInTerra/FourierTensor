import work_in_progress.OriginalScratchGroupedBodyRAM

/-! Actual original-width input/output wrapper for a shared scratch DAG.
Fixed role bits, bounded remainder bits, metadata and XOR tables, fresh
scratch initialization and clearing, and extraction all stay in native RAM.
Only original role count contributes the role bits in k=a+u*f+r. -/
namespace FourierSchur.OriginalScratchGroupedPhysicalRAM
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty Matrix Finset
open OriginalGroupedWordRAM OriginalGroupedRoleBitsRAM OriginalGroupedPhysicalBits
open OriginalNativeBankDAG OriginalScratchGroupedBodyRAM
open scoped BigOperators
noncomputable section
universe U
variable {α η κ : Type*} [Fintype α] [DecidableEq α]
  [Fintype η] [DecidableEq η] [Fintype κ] [DecidableEq κ] {ι : Type U}
set_option maxHeartbeats 1000000

theorem physical_body (cl : Paint) (m : Bool)
    (X : Layout α) (R0 : Layout η) (R : Layout (η⊕κ)) (j : η) (a r : ℕ)
    (hR : R0.n=2^a) (hr : 3≤X.n) (hd : r<X.n)
    (b : Bank (hatch cl) ι) (k f : ι→ℕ)
    (hk : ∀ i,X.n*f i+r+a=k i) (v : ∀ i,Bits (k i)→ℂ)
    (hB : Small b.B (fun i => 2^k i))
    (A : (η⊕κ)→OBase α) (tau : ι→ℕ→ℕ)
    (HC : ∀ n : ℕ,0<n → n≤X.n → GroupedResidual.Rig.RawContract cl b
      (fun i => n*f i) (fun i => tau i (n*f i)))
    (nodes : List (Node α η κ)) (D : Matrix η (η⊕κ) ℚ)
    (H : KernelDAG A nodes D) :
    Able m b (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i))
      (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i)
      (fun i => (nodes.map (nodeCharge X r (f i) (tau i))).sum) := by
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
  have HW := (macro_native b HZ R j hr A tau HC nodes D H).mono
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

end
end FourierSchur.OriginalScratchGroupedPhysicalRAM
