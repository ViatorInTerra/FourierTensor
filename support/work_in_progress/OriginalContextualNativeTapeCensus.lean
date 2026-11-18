import work_in_progress.OriginalContextualNativeTapeCorrectness
import work_in_progress.OriginalHellingerCallbackMoment

/-! Exact census and complete spectator-expanded charge of the verified
native tape. The strict square-root moment is not true for this inventory;
the final theorem records that fact for the actual generated program.
-/
namespace FourierSchur.OriginalContextualNativeTapeCensus
open OAI.PowerSaving OAI.PowerSaving.Binary Matrix Finset
open OriginalNativeBankDAG OriginalNativeFrameAlphabet OriginalContextualNativeTapeMetadata
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 30000

structure Census where
  empty : ℕ
  line : ℕ
  complement : ℕ
  full : ℕ
  deriving DecidableEq, Repr

def census : List Mode → Census
  | [] => ⟨0,0,0,0⟩
  | .empty::ms => {census ms with empty:=(census ms).empty+1}
  | .line _::ms => {census ms with line:=(census ms).line+1}
  | .complement _::ms => {census ms with complement:=(census ms).complement+1}
  | .full::ms => {census ms with full:=(census ms).full+1}

def bump (m : Mode) (c : Census) : Census :=
  match m with
  | .empty => {c with empty:=c.empty+1}
  | .line _ => {c with line:=c.line+1}
  | .complement _ => {c with complement:=c.complement+1}
  | .full => {c with full:=c.full+1}

theorem census_cons (m : Mode) (ms : List Mode) : census (m::ms)=bump m (census ms) := by
  cases m <;> rfl

theorem bump_comm (a b : Mode) (c : Census) : bump a (bump b c)=bump b (bump a c) := by
  cases a <;> cases b <;> rfl

theorem census_snoc (ms : List Mode) (m : Mode) : census (ms++[m])=bump m (census ms) := by
  induction ms with
  | nil => cases m <;> rfl
  | cons a ms ih => rw [List.cons_append,census_cons,ih,census_cons,bump_comm]

def rangeCensus (start : ℕ) : ℕ → Census
  | 0 => ⟨0,0,0,0⟩
  | len+1 => bump (modeAt (start+len)) (rangeCensus start len)

theorem census_range (start len : ℕ) :
    census (List.ofFn (fun i : Fin len => modeAt (start+i.val)))=rangeCensus start len := by
  induction len with
  | zero => rfl
  | succ len ih =>
    rw [List.ofFn_succ_last,census_snoc]
    simpa only [Fin.val_castSucc,Fin.val_last,rangeCensus] using
      congrArg (bump (modeAt (start+len))) ih

def score {R : Type*} [CommSemiring R] (c : Census) (z l p f : R) : R :=
  (c.empty:R)*z+(c.line:R)*l+(c.complement:R)*p+(c.full:R)*f

def price {R : Type*} (z l p f : R) : Mode → R
  | .empty => z
  | .line _ => l
  | .complement _ => p
  | .full => f

theorem score_census {R : Type*} [CommSemiring R] (ms : List Mode) (z l p f : R) :
    score (census ms) z l p f=(ms.map (price z l p f)).sum := by
  induction ms with
  | nil => simp [census,score]
  | cons m ms ih =>
    rw [List.map_cons,List.sum_cons,← ih]
    cases m <;> simp only [census,score,price,Nat.cast_add,Nat.cast_one] <;> ring

def modeRank : Mode → ℕ
  | .empty => 0
  | .line _ => 1
  | .complement _ => 215
  | .full => 216

theorem mode_card (m : Mode) : (modeMask m).card=modeRank m := by
  cases m <;> simp [modeMask,modeRank,Finset.card_sdiff]

theorem node_rank (i : Fin 2327) : nodeRank (nativeNode i)=modeRank (modeAt i.val) := by
  simp [nodeRank,nativeNode,mode_card]

def modes : List Mode := List.ofFn (fun i : Fin 2327 => modeAt i.val)

theorem actual_census : census modes=⟨191,88,88,1960⟩ := by
  have H := census_range 0 2327
  simp only [Nat.zero_add] at H
  unfold modes
  rw [H]
  decide +kernel

def chargeMode (r f : ℕ) (tau : ℕ → ℕ) : Mode → ℕ :=
  price 0 (2^r*(2^f)^215*tau f) (2^r*2^f*tau (215*f)) (2^r*tau (216*f))

theorem node_charge (r f : ℕ) (tau : ℕ → ℕ) (i : Fin 2327) :
    nodeCharge (Layout.std 216) r f tau (nativeNode i)=chargeMode r f tau (modeAt i.val) := by
  unfold nodeCharge
  rw [node_rank]
  change (if modeRank (modeAt i.val)=0 then 0 else
    2^r*(2^f)^(216-modeRank (modeAt i.val))*tau (modeRank (modeAt i.val)*f))=_
  cases hm : modeAt i.val <;> simp [modeRank,chargeMode,price]

theorem complete_charge (r f : ℕ) (tau : ℕ → ℕ) :
    (OriginalContextualNativeTapeImplementation.nodes.map
      (nodeCharge (Layout.std 216) r f tau)).sum=
      1960*(2^r*tau (216*f))+88*(2^r*2^f*tau (215*f))+
        88*(2^r*(2^f)^215*tau f) := by
  have hm : OriginalContextualNativeTapeImplementation.nodes.map (nodeCharge (Layout.std 216) r f tau)=
      modes.map (chargeMode r f tau) := by
    simp only [OriginalContextualNativeTapeImplementation.nodes,modes,List.map_ofFn]
    congr 1
    funext i
    exact node_charge r f tau i
  rw [hm]
  have H := score_census modes 0 (2^r*(2^f)^215*tau f)
    (2^r*2^f*tau (215*f)) (2^r*tau (216*f))
  rw [actual_census] at H
  unfold chargeMode
  rw [← H]
  simp only [score,Nat.cast_id,mul_zero,zero_add]
  ac_rfl

theorem complete_rank_sum :
    (OriginalContextualNativeTapeImplementation.nodes.map nodeRank).sum=442368 := by
  have hm : OriginalContextualNativeTapeImplementation.nodes.map nodeRank=modes.map modeRank := by
    simp only [OriginalContextualNativeTapeImplementation.nodes,modes,List.map_ofFn]
    congr 1
    funext i
    exact node_rank i
  rw [hm]
  have H := score_census modes (0:ℕ) 1 215 216
  have he : modes.map modeRank=modes.map (price (0:ℕ) 1 215 216) := by
    apply List.map_congr_left
    intro m _
    cases m <;> rfl
  rw [he,← H,actual_census]
  norm_num [score]

theorem normalized_order_eq_one :
    ((OriginalContextualNativeTapeImplementation.nodes.map nodeRank).sum:ℝ)/(2048*216)=1 := by
  rw [complete_rank_sum]
  norm_num

def improvedMoment : ℝ :=
  ((1960:ℝ)+88*Real.sqrt (215/216:ℝ)+88*Real.sqrt (1/216:ℝ))/2048

theorem improved_moment_above_one : 1 < improvedMoment := by
  have h1 : (997/1000:ℝ)≤Real.sqrt (215/216:ℝ) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
  have h2 : (68/1000:ℝ)≤Real.sqrt (1/216:ℝ) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
  unfold improvedMoment
  linarith

theorem improved_moment_gain :
    OriginalHellingerCallbackMoment.currentMoment-improvedMoment=
      3*Real.sqrt (1/216:ℝ)/2048 := by
  unfold improvedMoment OriginalHellingerCallbackMoment.currentMoment
  ring

theorem improved_moment_strictly_better :
    improvedMoment < OriginalHellingerCallbackMoment.currentMoment := by
  have hs : 0<Real.sqrt (1/216:ℝ) := Real.sqrt_pos.2 (by norm_num)
  have H := improved_moment_gain
  linarith

def squareRootMoment : ℝ :=
  (modes.map (fun m => Real.sqrt ((modeRank m:ℝ)/216))).sum/2048

theorem actual_square_root_moment :
    squareRootMoment=improvedMoment := by
  have H := score_census modes (0:ℝ) (Real.sqrt (1/216:ℝ))
    (Real.sqrt (215/216:ℝ)) 1
  have he : modes.map (fun m => Real.sqrt ((modeRank m:ℝ)/216))=
      modes.map (price (0:ℝ) (Real.sqrt (1/216:ℝ)) (Real.sqrt (215/216:ℝ)) 1) := by
    apply List.map_congr_left
    intro m _
    cases m <;> norm_num [modeRank,price]
  unfold squareRootMoment
  rw [he,← H,actual_census]
  unfold score improvedMoment
  norm_num
  ring

theorem actual_square_root_moment_above_one : 1<squareRootMoment := by
  rw [actual_square_root_moment]
  exact improved_moment_above_one

def programMoment : ℝ :=
  (OriginalContextualNativeTapeImplementation.nodes.map
    (fun g => Real.sqrt ((nodeRank g:ℝ)/216))).sum/2048

theorem program_moment_eq : programMoment=squareRootMoment := by
  unfold programMoment squareRootMoment
  have H : OriginalContextualNativeTapeImplementation.nodes.map (fun g => Real.sqrt ((nodeRank g:ℝ)/216))=
      modes.map (fun m => Real.sqrt ((modeRank m:ℝ)/216)) := by
    simp only [OriginalContextualNativeTapeImplementation.nodes,modes,List.map_ofFn]
    congr 1
    funext i
    simp only [Function.comp_apply]
    rw [node_rank]
  rw [H]

theorem program_moment_above_one : 1<programMoment := by
  rw [program_moment_eq]
  exact actual_square_root_moment_above_one

section Native
open OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
universe U
variable {ι : Type U} {m : Bool} {cl : Paint} {f : ι→ℕ}
  {s : Ty} {x : ι→T s} {r : ℕ}
  {v : ∀ i,Grain (Fin 216) (Fin 2048) r (f i)}

/-- The verified native RAM program with its exact, fully expanded child
bill. Local arithmetic, tables, addresses, memory and control are paid by
the native compiler at original input width, without a scratch denominator. -/
theorem native_kernel_charged (b : Bank (hatch cl) ι)
    (h : Rig m b.B f s x cl (Layout.std 216) (Layout.std 2048) r v)
    (R : Layout Role) (tau : ι→ℕ→ℕ)
    (HC : ∀ k : ℕ,0<k → k≤216 → GroupedResidual.Rig.RawContract cl b
      (fun i => k*f i) (fun i => tau i (k*f i))) :
    Able m b s (bundle cl) x
      (fun i => (fleet (Layout.std 216) R r (f i)).tape
        (OriginalLocalizedBankWorkspaceRAM.padded (κ:=Fin 2327)
          (OriginalContextualNativeTapeCorrectness.kernelGrain (v i))))
      (fun i => (fleet (Layout.std 216) (Layout.std 2048) r (f i)).n)
      (fun i => 1960*(2^r*tau i (216*f i))+88*(2^r*2^(f i)*tau i (215*f i))+
        88*(2^r*(2^(f i))^215*tau i (f i))) := by
  simpa only [complete_charge] using
    OriginalContextualNativeTapeCorrectness.native_kernel b h R tau HC

end Native

end
end FourierSchur.OriginalContextualNativeTapeCensus
