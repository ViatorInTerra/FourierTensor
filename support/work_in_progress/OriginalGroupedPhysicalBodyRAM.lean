import work_in_progress.OriginalGroupedPhysicalBits

/-! Concrete paid body wrapper for a retained grouped word. The physical
input partitions into the role bits, a bounded remainder, and amplified
column groups. Metadata preparation, the remainder, the fixed role bits,
all point/translation tokens, and every output coordinate are paid. -/
namespace FourierSchur.OriginalGroupedPhysicalBodyRAM
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty Matrix Finset
open OriginalGroupedWordRAM OriginalGroupedRoleBitsRAM OriginalGroupedPhysicalBits
open scoped BigOperators
noncomputable section
universe U
variable {α ρ : Type*} [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ] {ι : Type U}

theorem physical_body (cl : Paint) (m : Bool)
    (X : Layout α) (R : Layout ρ) (a r : Nat)
    (hR : R.n=2^a) (hr : 3≤X.n) (hd : r<X.n)
    (b : Bank (hatch cl) ι) (k f : ι → Nat)
    (hk : ∀ i, X.n*f i+r+a=k i)
    (v : ∀ i, Bits (k i) → ℂ)
    (hB : Small b.B (fun i => 2^k i))
    (A : ρ → OBase α) (tau : ι → Nat → Nat)
    (HF : FrameService (m:=m) (f:=f) (X:=X) (R:=R) (r:=r) A b tau)
    (P : OriginalGroupedFrameWords.Word α ρ)
    (hp : ∀ f x, OriginalGroupedFrameWords.walk A f P x=
      multiAct f (fun _ => kernel α) x) :
    Able m b (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i))
      (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i)
      (fun i => wordCharge X r (f i) (tau i) P) := by
  let W i := 2^k i
  let env i := givenBits cl (k i) (v i)
  let e i := physicalSerial X R a r (f i) (k i) hR (hk i)
  let inp i : Grain α ρ r (f i) := fun q => v i (e i q)
  let z i := remnant r (f i) (inp i)
  have hsize (i) : (fleet X R r (f i)).n=W i := physical_size X R a r (f i) (k i) hR (hk i)
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
  have HI : Rig m b.B f T2 env2 cl X R r inp := by
    have H : Has m b.B T2 (simIn cl) env2 env := Can.fst Can.first
    refine ⟨⟨Can.snd (Can.snd Can.first),Can.fst (Can.snd Can.first),Can.second,hm⟩,
      H.snd.fst,?_⟩
    exact H.snd.snd.cong (fun _ => rfl)
      (fun i => (physical_tape X R a r (f i) (k i) hR (hk i) (v i)).symm)
  have HD : Can m b.B T2 (bundle cl) env2
      (fun i => (fleet X R r (f i)).tape (z i)) W := by
    simpa only [hsize] using HI.dots_cost
  let T3 := p T2 (bundle cl)
  let env3 i : Ty.T T3 := (env2 i,(fleet X R r (f i)).tape (z i))
  have hz := HI.gather id env3 (t:=T3) Can.first
  have HZ : Rig m b.B f T3 env3 cl X R r z := ⟨hz.gear,hz.imag,Can.second⟩
  have HW := (sweep A b tau HF HZ P).mono
    (fun i => (hsize i).le) (fun _ => le_rfl)
  let y i := coastline A r (f i) P (z i)
  let T4 := p T3 (bundle cl)
  let env4 i : Ty.T T4 := (env3 i,(fleet X R r (f i)).tape (y i))
  have hy := HZ.gather id env4 (t:=T4) Can.first
  have HY : Rig m b.B f T4 env4 cl X R r y := ⟨hy.gear,hy.imag,Can.second⟩
  have HA := roleKernel_cost HY (roleIndex R hR)
  have HE (i) : (fleet X R r (f i)).tape (roleKernelPoint (roleIndex R hR) (y i)) =
      (bits (k i)).tape (ripple (k i) (v i)) := by
    have hfun : roleKernelPoint (roleIndex R hR) (y i)=
        (fun q => ripple (k i) (v i) (e i q)) := by
      funext q
      exact full_kernel X R a r (f i) (k i) hR (hk i) A P (hp _) (v i) q
    rw [hfun]
    exact physical_tape X R a r (f i) (k i) hR (hk i) _
  have HO := (Able.of_can (b:=b) (HA.mono (fun i => (hsize i).le))).cong
    (fun _ => rfl) HE
  have HT := (Able.of_can (b:=b) HP).save_keep
    ((Able.of_can (b:=b) HX).save_keep ((Able.of_can (b:=b) HD).save_keep
      (HW.save_keep HO)))
  simpa only [Nat.zero_add,Nat.add_zero,hsize] using HT

end
end FourierSchur.OriginalGroupedPhysicalBodyRAM
