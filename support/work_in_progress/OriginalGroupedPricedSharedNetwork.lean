import work_in_progress.OriginalGroupedFrameBudget

/-! The existing native all-role shared network, retaining complete residual
frame blocks and their exact first-moment inventory. The path proofs reuse
the archived finite labels and gate synchronization. This is an operator
and recursive-inventory certificate; points/translations/routing are paid
by the separate native RAM compiler. -/
namespace FourierSchur.OriginalGroupedPricedSharedNetwork
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.Cluster Matrix Finset
open OriginalGroupedFrameWords OriginalGroupedFrameBudget
noncomputable section

def DPath (j : J) (F : StartAxes) (s t : Lab) (M : Q) (d : ℕ) : Prop :=
  let A := basisBox j F
  ∃ N : Q, M * N = 1 ∧ OriginalGroupedFrameBudget.Path A s t (actPoint M) d ∧ OriginalGroupedFrameBudget.Path A s t (actPoint Nᵀ) d

lemma rat_if (P : Prop) [Decidable P] :
    (((if P then 1 else 0):ℚ):ℂ) = if P then 1 else 0 := by split <;> simp_all

lemma ap_one : actPoint (1:Q) = id := by
  funext x i
  unfold actPoint
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ h
    simp [one_apply,Ne.symm h]
  · simp
lemma ap_mul (M N : Q) :
    actPoint (M*N) = actPoint M ∘ actPoint N := by
  funext x i
  simp only [actPoint, Function.comp_apply, Matrix.mul_apply, Rat.cast_sum, Rat.cast_mul,
    sum_mul,mul_sum,_root_.mul_assoc]
  rw [sum_comm]

namespace DPath
variable {j : J} {F : StartAxes} {s t u : Lab} {M N : Q} {d e : ℕ}

lemma of_id (h : OriginalGroupedFrameBudget.Path (basisBox j F) s t id d) : DPath j F s t 1 d := by
  refine ⟨1,mul_one _,?_,?_⟩ <;> simpa [ap_one]

lemma trans (a : DPath j F s t M d) (b : DPath j F t u N e) :
    DPath j F s u (N*M) (d+e) := by
  obtain ⟨x,hx,hm,hn⟩ := a
  obtain ⟨y,hy,hl,hk⟩ := b
  refine ⟨x*y,?_,?_,?_⟩
  · rwa [Matrix.mul_assoc, ← Matrix.mul_assoc M, hx, one_mul]
  · rw [ap_mul]
    exact hm.trans hl
  · rw [transpose_mul, ap_mul]
    exact hn.trans hk

lemma paired (h : M*M=0) (g : syncBox j F s M) :
    DPath j F s s (1+M) 0 ∧ DPath j F s s (1-M) 0 := by
  have cond (i k) (h : M i k≠0) :
      frame (basisBox j F i) (s i) = frame (basisBox j F k) (s k) :=
    frame_congr _ _ _ _ (g i k h)
  constructor
  · refine ⟨1-M,inv_one_add h,OriginalGroupedFrameBudget.Path.gate _ ?_,OriginalGroupedFrameBudget.Path.gate _ ?_⟩
    · intro i k h
      by_cases hik : i=k
      · subst k; rfl
      · apply cond i k; simpa [one_apply,hik] using h
    · intro i k h
      by_cases hik : k=i
      · subst k; rfl
      · exact (cond k i (by simpa [one_apply,hik] using h)).symm
  · refine ⟨1+M,inv_one_sub h,OriginalGroupedFrameBudget.Path.gate _ ?_,OriginalGroupedFrameBudget.Path.gate _ ?_⟩
    · intro i k h
      by_cases hik : i=k
      · subst k; rfl
      · apply cond i k; simpa [one_apply,hik] using h
    · intro i k h
      by_cases hik : k=i
      · subst k; rfl
      · exact (cond k i (by simpa [one_apply,hik] using h)).symm

lemma rise (g : ∀ i, s i ⊆ t i) : DPath j F s t 1 0 :=
  of_id (OriginalGroupedFrameBudget.Path.inc _ g)

end DPath

theorem invocation_path (j : J) (F : StartAxes) :
    DPath j F (bp j) (bend j) (1+eXY) (33*32) := by
  have h0 := DPath.paired zero_JJ (sync0 j F) |>.2
  have h1 := DPath.paired zero_RR (sync1 j F) |>.2
  have h2 := DPath.paired zero_VV (sync2 j F) |>.1
  have h3 := DPath.paired zero_GG (sync3 j F) |>.1
  have h4 := DPath.paired zero_RR (sync4 j F) |>.1
  have h5 := DPath.paired zero_JJ (sync5 j F) |>.1
  have h6 := DPath.paired zero_GG (sync6 j F) |>.2
  have h7 := DPath.paired zero_VV (sync7 j F) |>.2
  have rise : ∀ {u v : Lab}, (∀ i, u i ⊆ v i) → DPath j F u v 1 0 := fun h => DPath.rise h
  have down : DPath j F (b3 j) (b4 j) 1 (33*32) := by
    rw [← loss34 j]; exact DPath.of_id (OriginalGroupedFrameBudget.Path.reframe ..)
  have H0 := (rise (inc_bp_b0 j)).trans h0
  have H1 := H0.trans (rise (inc_b0_b1 j)) |>.trans h1
  have H2 := H1.trans (rise (inc_b1_b2 j)) |>.trans h2
  have H3 := H2.trans (rise (inc_b2_b3 j)) |>.trans h3
  have H4 := H3.trans down |>.trans h4
  have H5 := H4.trans (rise (inc_b4_b5 j)) |>.trans h5
  have H6 := H5.trans (rise (inc_b5_b6 j)) |>.trans h6
  have H7 := H6.trans (rise (inc_b6_b7 j)) |>.trans h7
  have Hl := H7.trans (rise (inc_b7_bend j))
  rw [← net_eq, net]
  simpa only [← Matrix.mul_assoc,mul_one,one_mul,Nat.zero_add,Nat.add_zero] using Hl

/-- Induced logical actions. -/
def forward (x : Box→ℂ) : Box→ℂ
  | .inl (.inr i) => x (byy i) + x (bx i)
  | r => x r

def backward (x : Box→ℂ) : Box→ℂ
  | .inl (.inl i) => x (bx i) - x (byy i)
  | r => x r

lemma ap_add (M N : Q) (x : Box→ℂ) (r : Box) :
    actPoint (M+N) x r = actPoint M x r + actPoint N x r := by
  simp [actPoint, _root_.add_mul,sum_add_distrib]
lemma ap_sub (M N : Q) (x : Box→ℂ) (r : Box) :
    actPoint (M-N) x r = actPoint M x r - actPoint N x r := by
  simp [actPoint, _root_.sub_mul,sum_sub_distrib]

lemma ap_f : actPoint (1+eXY)=forward := by
  funext x i
  rw [ap_add, ap_one]
  rcases i with ((i|i)|(i|i)) <;>
    simp [actPoint, Fintype.sum_sum_type, eXY, one_apply, rat_if, ite_mul, forward]

lemma ap_b : actPoint (1-eXY)ᵀ=backward := by
  funext x i
  rw [transpose_sub, transpose_one, ap_sub, ap_one]
  rcases i with ((i|i)|(i|i)) <;>
    simp [actPoint, Fintype.sum_sum_type, eXY, one_apply, rat_if, ite_mul, backward]

theorem invocation (j : J) (F : StartAxes) :
    OriginalGroupedFrameBudget.Path (basisBox j F) (bp j) (bend j) forward (33*32) ∧
    OriginalGroupedFrameBudget.Path (basisBox j F) (bp j) (bend j) backward (33*32) := by
  obtain ⟨N, hN, H, G⟩ := invocation_path j F
  have h : N=1-eXY := by
    calc
      N = ((1-eXY)*(1+eXY))*N := by rw [inv_one_sub zero_XX, one_mul]
      _ = _ := by rw [Matrix.mul_assoc,hN,mul_one]
  subst N
  exact ⟨ap_f ▸ H,ap_b ▸ G⟩

lemma stage (rev : Bool) (j : J) :
    OriginalGroupedFrameBudget.Path bases (border j.val) (border (j.val+1)) (stageOp rev) stageLoss := by
  let d : Other j → ℕ := fun _ => 33*32
  have hd : stageLoss=∑ i, d i := by
    dsimp only [d]
    rw [sum_const,card_univ,card_other]
    simp [stageLoss]
  rw [hd]
  let h := fun _ : Other j => if rev then backward else forward
  apply OriginalGroupedFrameBudget.Path.parallel (position j) (pos_dis j) bases (h:=h)
  · intro i
    rw [bases_local,border_bp,border_end]
    cases rev
    · exact (invocation j (axes j i)).1
    · exact (invocation j (axes j i)).2
  · intro i x
    funext r
    rcases r with ((r|r)|(r|r)) <;> cases rev <;> rfl
  · rintro x ((k|k)|r) hr
    · exfalso; specialize hr (omitJ j k); apply hr; rw [cover_iff]; exact ⟨bx (k j), congr_arg gx (locate_omit ..)⟩
    · exfalso; specialize hr (omitJ j k); apply hr; rw [cover_iff]; exact ⟨byy (k j), congr_arg gy (locate_omit ..)⟩
    · rfl
  · rintro ((k|k)|(⟨i,p,a⟩|r)) hr
    · exfalso; specialize hr (omitJ j k); apply hr; rw [cover_iff]; exact ⟨bx (k j), congr_arg gx (locate_omit ..)⟩
    · exfalso; specialize hr (omitJ j k); apply hr; rw [cover_iff]; exact ⟨byy (k j), congr_arg gy (locate_omit ..)⟩
    · by_cases ig : i=j
      · subst i; exfalso; specialize hr p; apply hr; rw [cover_iff]; exact ⟨.inr a,rfl⟩
      · change (if i.val < j.val then univ else ∅) =
          (if i.val < j.val + 1 then univ else ∅)
        have h : i.val≠j.val := fun h => ig (Fin.ext h)
        simp only [show (i.val < j.val+1) ↔ (i.val < j.val) from (by omega)]
    · rfl


lemma all_stages : OriginalGroupedFrameBudget.Path bases (border 0) sink exchange (3*stageLoss) := by
  have h := ((stage false 0).trans (stage true 1)).trans (stage false 2)
  change OriginalGroupedFrameBudget.Path _ (border 0) (border 3)
    (stageOp false ∘ stageOp true ∘ stageOp false) ((stageLoss+stageLoss)+stageLoss) at h
  have g := h.trans (OriginalGroupedFrameBudget.Path.inc bases border_le_sink)
  have he : id ∘ (stageOp false ∘ stageOp true ∘ stageOp false) = exchange := by
    funext x r
    rcases r with (k|k)|r <;> simp [Function.comp_apply, stageOp,exchange,gx,gy]
  rw [he, show stageLoss+stageLoss+stageLoss+0=3*stageLoss by omega] at g
  exact g


private lemma c_tally (a b c : ℕ) (h : a + b = c + 2*(3*stageLoss))
  (g : b=4060^3) (k : c+4060^3=tower*mcol) : (a+0)+0=nMoves := by
  unfold nMoves; norm_num [tower,mcol,bankSave,stageLoss] at *; omega


/-- Whole grouped frame blocks retain all inputs in every native role.
Their sum of dimensions equals the archived exact directional inventory;
this equality is not an assumption about a faster backend. -/
theorem certificate :
    ∃ p : OriginalGroupedFrameWords.Word Blocks Role,
      OriginalGroupedFrameBudget.firstMoment p=nMoves ∧
      ∀ f (x : Data Blocks Role f),
        OriginalGroupedFrameWords.walk bases f p x=multiAct f (fun _ => kernel Blocks) x := by
  obtain ⟨p,hp,he⟩ := all_stages
  refine ⟨p++[.translate correction,.localM recoverM],?_,?_⟩
  · rw [OriginalGroupedFrameBudget.firstMoment_append]
    simpa [OriginalGroupedFrameBudget.firstMoment,OriginalGroupedFrameBudget.moveMoment]
      using c_tally (OriginalGroupedFrameBudget.firstMoment p) _ _ hp mass_border mass_sink
  · intro f x
    obtain ⟨y,rfl⟩ := framed_surj bases (border 0) f x
    rw [OriginalGroupedFrameWords.walk_append,he]
    simp only [OriginalGroupedFrameWords.walk,List.foldl_cons,List.foldl_nil,
      OriginalGroupedFrameWords.Move.go,recover_eq]
    exact netEffect f y

end
end FourierSchur.OriginalGroupedPricedSharedNetwork
