import work_in_progress.OriginalScratchGroupedPhysicalRAM
import work_in_progress.OriginalProjectionNativeTapeCensus

/-! Close the actual initialized-scratch physical body at every tensor order.
The only recursive hypotheses are Desc.works for strictly smaller orders.
The role denominator is the original role count; fresh scratch is excluded.
The concrete projection instance below has no improved moment assertion. -/
namespace FourierSchur.OriginalScratchGroupedInstantiationRAM
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty Matrix Finset
open OriginalGroupedRecursionRAM OriginalGroupedFrameCompilerRAM
open OriginalNativeBankDAG OriginalScratchGroupedBodyRAM OriginalScratchGroupedPhysicalRAM
open scoped BigOperators
noncomputable section
variable {α : Type*} {η κ : Type} [Fintype α] [DecidableEq α]
  [Fintype η] [DecidableEq η] [Fintype κ] [DecidableEq κ]
set_option maxHeartbeats 1000000

theorem open_body (cl : Paint) (m : Bool)
    (X : Layout α) (R0 : Layout η) (R : Layout (η⊕κ)) (j : η)
    (a : ℕ) (ha : 0<a) (hR : R0.n=2^a) (hu : 3≤X.n)
    (A : (η⊕κ)→OBase α) (nodes : List (Node α η κ)) (D : Matrix η (η⊕κ) ℚ)
    (Hsem : KernelDAG A nodes D) :
    OpenBody (OriginalGroupedWordProfile.scheme (programWord nodes D) a ha) cl m := by
  let P := programWord nodes D
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
      (fun i => (l i).v) (Small.self _) A tau HC nodes D Hsem
    apply H.mono (fun _ => le_rfl)
    intro i
    change (nodes.map (nodeCharge X r (f i) (tau i))).sum ≤
      childCharge (OriginalGroupedWordProfile.scheme P a ha) (k i) (tau i)
    rw [OriginalGroupedWordProfile.charge_eq_wordCharge P a ha X r (f i) (k i)
      hr (by have Hk := hk i; omega) (hf i)]
    exact (programWord_charge X r (f i) (tau i) nodes D).symm.le
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
    (A : (η⊕κ)→OBase α) (nodes : List (Node α η κ)) (D : Matrix η (η⊕κ) ℚ)
    (Hsem : KernelDAG A nodes D)
    {ι : Type} (k : ι→ℕ) (v : ∀ i,Bits (k i)→ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i))
      (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => allowance (OriginalGroupedWordProfile.scheme (programWord nodes D) a ha) (k i)) :=
  close_grouped_body _ cl m (open_body cl m X R0 R j a ha hR hu A nodes D Hsem) k v

/-- The currently verified projection DAG now yields a closed all-order
program, without a supplied fast backend or a new exponent claim.  Its
recurrence is its own exact word inventory at 2048 ORIGINAL roles. -/
theorem projection_program (cl : Paint) (m : Bool)
    {ι : Type} (k : ι→ℕ) (v : ∀ i,Bits (k i)→ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i))
      (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => allowance (OriginalGroupedWordProfile.scheme
        OriginalProjectionNativeTapeImplementation.program 11 (by decide)) (k i)) := by
  apply grouped_program cl m (Layout.std 125) (Layout.std 2048)
    (Layout.someLayout OriginalProjectionNativeTapeImplementation.Role) (0 : Fin 2048)
    11 (by decide) (by norm_num [Layout.std]) (by norm_num [Layout.std])
    OriginalProjectionNativeTapeImplementation.bases
    OriginalProjectionNativeTapeImplementation.nodes
    OriginalProjectionNativeTapeImplementation.outputs
  intro f x j
  exact OriginalProjectionNativeTapeCorrectness.word_original_kernel f x j

end
end FourierSchur.OriginalScratchGroupedInstantiationRAM
