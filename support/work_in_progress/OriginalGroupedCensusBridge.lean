import work_in_progress.OriginalGroupedNativeInventory
import work_in_progress.OriginalGroupedWordProfile

/-! Witness-level rank accounting for native grouped words.  The same word
which proves the operator identity carries an arbitrary zero-at-zero rank
cost.  In particular, role embeddings do not create spectator-free calls.
The final theorems expose the nine actual frame transitions of each native
invocation and their complete three-stage composition. -/

namespace FourierSchur.OriginalGroupedCensusBridge

open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.Cluster Matrix Finset
open OriginalGroupedFrameWords OriginalGroupedFrameBudget
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000

variable {α : Type*} {ρ σ : Type} [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ] [Fintype σ] [DecidableEq σ]

private theorem indicator_sum (P : ρ → Prop) [DecidablePred P] (v : ℝ) :
    (∑ r : ρ, if P r then v else 0) =
      (Fintype.card {r : ρ // P r}:ℝ)*v := by
  rw [← Fintype.sum_subtype_add_sum_subtype P]
  have ht (r : {r : ρ // P r}) : (if P r.val then v else 0)=v := if_pos r.property
  have hf (r : {r : ρ // ¬P r}) : (if P r.val then v else 0)=0 := if_neg r.property
  simp_rw [ht,hf]
  simp only [sum_const,sum_const_zero,card_univ,nsmul_eq_mul,mul_zero,add_zero]

def frameCost (s t : ρ → Finset α) (c : ℕ → ℝ) : ℝ :=
  ∑ r, c (changeSize (s r) (t r))

def moveCost (c : ℕ → ℝ) : OriginalGroupedFrameWords.Move α ρ → ℝ
  | .frames s t => frameCost s t c
  | _ => 0

def wordCost (p : Word α ρ) (c : ℕ → ℝ) : ℝ := (p.map (moveCost c)).sum

theorem wordCost_append (p q : Word α ρ) (c : ℕ → ℝ) :
    wordCost (p++q) c = wordCost p c + wordCost q c := by
  simp [wordCost]

theorem moveCost_over (e : ρ ↪ σ) (m : OriginalGroupedFrameWords.Move α ρ)
    (c : ℕ → ℝ) (hc : c 0=0) : moveCost c (m.over e)=moveCost c m := by
  cases m with
  | localM M => rfl
  | translate z => rfl
  | frames s t =>
    change (∑ r, c (changeSize (extend e ∅ s r) (extend e ∅ t r))) =
      ∑ r, c (changeSize (s r) (t r))
    rw [← sum_add_sum_compl (covered e)]
    have hz : ∑ r∈(covered e)ᶜ,
        c (changeSize (extend e ∅ s r) (extend e ∅ t r))=0 := by
      apply sum_eq_zero
      intro r hr
      have h := mem_compl.mp hr
      simp [extend_off e _ _ h,changeSize,hc]
    rw [hz,add_zero,covered,sum_map]
    simp

theorem wordCost_over (e : ρ ↪ σ) (p : Word α ρ)
    (c : ℕ → ℝ) (hc : c 0=0) :
    wordCost (p.map (OriginalGroupedFrameWords.Move.over e)) c=wordCost p c := by
  simp [wordCost,List.map_map,Function.comp_def,moveCost_over e _ c hc]

theorem moveCost_eq (c : ℕ → ℝ) (hc : c 0=0)
    (m : OriginalGroupedFrameWords.Move α ρ) :
    moveCost c m = ∑ r, c (OriginalGroupedWordProfile.moveRank m r) := by
  cases m with
  | frames s t =>
    simp [moveCost,frameCost,OriginalGroupedWordProfile.moveRank,
      OriginalGroupedWordProfile.residualRank_eq]
  | localM M => simp [moveCost,OriginalGroupedWordProfile.moveRank,hc]
  | translate z => simp [moveCost,OriginalGroupedWordProfile.moveRank,hc]

theorem wordCost_eq (p : Word α ρ) (c : ℕ → ℝ) (hc : c 0=0) :
    wordCost p c = ∑ q : OriginalGroupedWordProfile.Kind p,
      c (OriginalGroupedWordProfile.rank p q) := by
  symm
  change (∑ q : Fin p.length × ρ,
    c (OriginalGroupedWordProfile.moveRank (p.get q.1) q.2)) = _
  rw [Fintype.sum_prod_type]
  simp_rw [← moveCost_eq c hc]
  rw [← Fin.sum_ofFn,List.ofFn_comp',List.ofFn_get]
  rfl

def momentCost (u a : ℕ) (z : ℝ) (r : ℕ) : ℝ :=
  if r=0 then 0 else (1/(2:ℝ)^a)*((r:ℝ)/(u:ℝ))^z

theorem moment_eq_wordCost (p : Word α ρ) (u a : ℕ) (z : ℝ) :
    OriginalGroupedWordProfile.moment p u a z = wordCost p (momentCost u a z) := by
  rw [wordCost_eq p _ (by simp [momentCost])]
  unfold OriginalGroupedWordProfile.moment
  apply sum_congr rfl
  intro q hq
  by_cases h : OriginalGroupedWordProfile.rank p q=0 <;>
    simp [OriginalGroupedWordProfile.weight,momentCost,h]

/-- An exact path, together with a cost identity for its own witness word.
No histogram of a different program is attached to the witness. -/
def CPath (A : ρ → OBase α) (s t : ρ → Finset α)
    (g : (ρ→ℂ)→(ρ→ℂ)) (profile : (ℕ → ℝ) → ℝ) : Prop :=
  ∃ p : Word α ρ,
    (∀ c : ℕ → ℝ, c 0=0 → wordCost p c=profile c) ∧
    ∀ f x, OriginalGroupedFrameWords.walk A f p (withFrame A s f x)=
      withFrame A t f (point f g x)

namespace CPath
variable {A : ρ → OBase α} {s t u : ρ → Finset α}

theorem refl : CPath A s s id (fun _ => 0) := by
  refine ⟨[],?_,?_⟩
  · intro c hc; rfl
  · intro f x; rfl

theorem trans {g h} {a b : (ℕ → ℝ) → ℝ}
    (p : CPath A s t g a) (q : CPath A t u h b) :
    CPath A s u (h∘g) (fun c => a c+b c) := by
  obtain ⟨p,hp,ap⟩ := p
  obtain ⟨q,hq,aq⟩ := q
  refine ⟨p++q,?_,?_⟩
  · intro c hc
    rw [wordCost_append,hp c hc,hq c hc]
  · intro f x
    rw [OriginalGroupedFrameWords.walk_append,ap,aq]
    rfl

theorem reframe (A : ρ → OBase α) (s t : ρ → Finset α) :
    CPath A s t id (frameCost s t) := by
  refine ⟨[.frames s t],?_,?_⟩
  · intro c hc
    simp [wordCost,moveCost]
  · intro f x
    funext r
    simp [OriginalGroupedFrameWords.walk,OriginalGroupedFrameWords.Move.go,
      withFrame,multiAct,matAct_mul,Matrix.mul_assoc,unframe_left]
    rfl

theorem gate (M : Matrix ρ ρ ℚ)
    (cond : ∀ i j, M i j≠0 → frame (A i) (s i)=frame (A j) (s j)) :
    CPath A s s (actPoint M) (fun _ => 0) := by
  refine ⟨[.localM M],?_,?_⟩
  · intro c hc; simp [wordCost,moveCost]
  · intro f x
    let T (r : ρ) := digitProd (fun _ : Fin f => frame (A r) (s r))
    funext r i
    change ∑ j, (M r j:ℂ)*(∑ a, T j i a*x j a) =
      ∑ a, T r i a*(∑ j, (M r j:ℂ)*x j a)
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro a ha
    apply sum_congr rfl
    intro j hj
    by_cases h : M r j=0
    · simp [h]
    · dsimp only [T]
      rw [cond r j h]
      ac_rfl

theorem lift (e : ρ ↪ σ) (A : σ → OBase α) {s t : σ → Finset α}
    {g : (σ→ℂ)→(σ→ℂ)} {h : (ρ→ℂ)→(ρ→ℂ)}
    {profile : (ℕ → ℝ) → ℝ}
    (q : CPath (A∘e) (s∘e) (t∘e) h profile)
    (hin : ∀ x, (g x)∘e=h (x∘e))
    (hout : ∀ x r, r∉covered e → g x r=x r)
    (he : ∀ r, r∉covered e → s r=t r) : CPath A s t g profile := by
  obtain ⟨p,hp,ha⟩ := q
  refine ⟨p.map (OriginalGroupedFrameWords.Move.over e),?_,?_⟩
  · intro c hc
    rw [wordCost_over e p c hc,hp c hc]
  · intro f x
    have frame_cont (s : σ → Finset α) (x : Data α σ f) :
        withFrame A s f x∘e=withFrame (A∘e) (s∘e) f (x∘e) := rfl
    have point_cont : point f g x∘e=point f h (x∘e) := by
      funext i j
      exact congr_fun (hin _) i
    funext r
    by_cases hr : r∈covered e
    · obtain ⟨j,rfl⟩ := (cover_iff ..).mp hr
      exact congr_fun (show OriginalGroupedFrameWords.walk A f _ _∘e=
        withFrame A t f _∘e by
        rw [OriginalGroupedFrameWords.walk_over,frame_cont,ha,frame_cont,point_cont]) j
    · rw [OriginalGroupedFrameWords.walk_out e A p _ _ hr]
      unfold withFrame multiAct
      simp only [he r hr]
      apply congrArg
      funext j
      exact (hout (fun r => x r j) r hr).symm

theorem parallel {I : Type*} [Fintype I] [DecidableEq I] (e : I → ρ ↪ σ)
    (dis : ∀ i j, i≠j → ∀ r∈covered (e i), r∉covered (e j))
    (A : σ → OBase α) {s t : σ → Finset α}
    {profile : I → (ℕ → ℝ) → ℝ}
    {g : (σ→ℂ)→(σ→ℂ)} {h : I → (ρ→ℂ)→(ρ→ℂ)}
    (q : ∀ i, CPath (A∘e i) (s∘e i) (t∘e i) (h i) (profile i))
    (hin : ∀ i x, (g x)∘e i=h i (x∘e i))
    (hout : ∀ x r, (∀ i, r∉covered (e i)) → g x r=x r)
    (he : ∀ r, (∀ i, r∉covered (e i)) → s r=t r) :
    CPath A s t g (fun c => ∑ i,profile i c) := by
  let u (j : Finset I) := j.biUnion fun i => covered (e i)
  let l (j : Finset I) (r : σ) := if r∈u j then t r else s r
  let k (j : Finset I) (x : σ→ℂ) (r : σ) := if r∈u j then g x r else x r
  have hh (j : Finset I) :
      CPath A s (l j) (k j) (fun c => ∑ i∈j,profile i c) := by
    induction j using Finset.induction with
    | empty =>
      simpa only [k,l,u,biUnion_empty,notMem_empty,ite_false,sum_empty] using
        (CPath.refl (A:=A) (s:=s))
    | insert i j hi ih =>
      have hiu (r) (hr : r∈covered (e i)) : r∉u j := by
        intro hg
        obtain ⟨w,hw,he'⟩ := mem_biUnion.mp hg
        have hw' : i≠w := by intro H; subst w; exact hi hw
        exact dis _ _ hw' r hr he'
      have hui (r) : r∈u (insert i j) ↔ r∈covered (e i) ∨ r∈u j := by
        simp [u]
      let fn (x : σ→ℂ) (r : σ) := if r∈covered (e i) then g x r else x r
      have compi (x) : fn x∘e i=h i (x∘e i) := by
        rw [← hin]
        funext r; simp [fn,covered]
      have gg : CPath A (l j) (l (insert i j)) fn (profile i) := by
        apply CPath.lift (e i) A (h:=h i) _ compi
        · intro x r hr; simp [fn,hr]
        · intro r hr; simp [l,hui,hr]
        · have eq1 : l j∘e i=s∘e i := by
            funext r
            have H : e i r∈covered (e i) := by simp [covered]
            simp [l,hiu _ H]
          have eq2 : l (insert i j)∘e i=t∘e i := by
            funext r
            have H : e i r∈covered (e i) := by simp [covered]
            simp [l,hui,H]
          rw [eq1,eq2]
          exact q i
      have cmp : fn∘k j=k (insert i j) := by
        funext x r
        by_cases hqr : r∈covered (e i)
        · obtain ⟨r,rfl⟩ := (cover_iff ..).mp hqr
          have eq : k j x∘e i=x∘e i := by
            funext r
            have H : e i r∈covered (e i) := by simp [covered]
            simp [k,hiu _ H]
          have H := congr_fun (show fn (k j x)∘e i=g x∘e i by
            rw [compi,eq,hin]) r
          exact H.trans (by simp [k,hui,hqr])
        · simp [Function.comp,k,fn,hui,hqr]
      have ht := ih.trans gg
      rw [cmp] at ht
      convert ht using 1
      funext c
      rw [sum_insert hi]
      ring
  have ha (r) : r∉u univ ↔ ∀ i, r∉covered (e i) := by simp [u]
  have eq1 : l univ=t := by
    funext r; by_cases H : r∈u univ
    · simp [l,H]
    · simp [l,H,he r ((ha r).1 H)]
  have eq2 : k univ=g := by
    funext x r; by_cases H : r∈u univ
    · simp [k,H]
    · simp [k,H,hout x r ((ha r).1 H)]
  have H := hh univ
  rwa [eq1,eq2] at H

end CPath

/-! The native invocation.  Costs below refer to the ACTUAL nine complete
frame changes.  The intervening eight rational local maps have zero
recursive cost; their scalar execution and routing remain paid elsewhere. -/

def invocationCost (j : J) (c : ℕ → ℝ) : ℝ :=
  frameCost (bp j) (b0 j) c + frameCost (b0 j) (b1 j) c +
  frameCost (b1 j) (b2 j) c + frameCost (b2 j) (b3 j) c +
  frameCost (b3 j) (b4 j) c + frameCost (b4 j) (b5 j) c +
  frameCost (b5 j) (b6 j) c + frameCost (b6 j) (b7 j) c +
  frameCost (b7 j) (bend j) c

def CDPath (j : J) (F : StartAxes) (s t : Lab) (M : Q)
    (profile : (ℕ → ℝ) → ℝ) : Prop :=
  let A := basisBox j F
  ∃ N : Q, M*N=1 ∧ CPath A s t (actPoint M) profile ∧
    CPath A s t (actPoint Nᵀ) profile

namespace CDPath
variable {j : J} {F : StartAxes} {s t u : Lab} {M N : Q}
  {a b : (ℕ → ℝ) → ℝ}

theorem of_id (h : CPath (basisBox j F) s t id a) : CDPath j F s t 1 a := by
  refine ⟨1,mul_one _,?_,?_⟩ <;>
    simpa [OriginalGroupedPricedSharedNetwork.ap_one]

theorem trans (p : CDPath j F s t M a) (q : CDPath j F t u N b) :
    CDPath j F s u (N*M) (fun c => a c+b c) := by
  obtain ⟨x,hx,hm,hn⟩ := p
  obtain ⟨y,hy,hl,hk⟩ := q
  refine ⟨x*y,?_,?_,?_⟩
  · rwa [Matrix.mul_assoc,← Matrix.mul_assoc M,hx,one_mul]
  · rw [OriginalGroupedPricedSharedNetwork.ap_mul]
    exact hm.trans hl
  · rw [transpose_mul,OriginalGroupedPricedSharedNetwork.ap_mul]
    exact hn.trans hk

theorem paired (h : M*M=0) (g : syncBox j F s M) :
    CDPath j F s s (1+M) (fun _ => 0) ∧
    CDPath j F s s (1-M) (fun _ => 0) := by
  have cond (i k) (h : M i k≠0) :
      frame (basisBox j F i) (s i)=frame (basisBox j F k) (s k) :=
    frame_congr _ _ _ _ (g i k h)
  constructor
  · refine ⟨1-M,inv_one_add h,CPath.gate _ ?_,CPath.gate _ ?_⟩
    · intro i k h
      by_cases hik : i=k
      · subst k; rfl
      · apply cond i k; simpa [one_apply,hik] using h
    · intro i k h
      by_cases hik : k=i
      · subst k; rfl
      · exact (cond k i (by simpa [one_apply,hik] using h)).symm
  · refine ⟨1+M,inv_one_sub h,CPath.gate _ ?_,CPath.gate _ ?_⟩
    · intro i k h
      by_cases hik : i=k
      · subst k; rfl
      · apply cond i k; simpa [one_apply,hik] using h
    · intro i k h
      by_cases hik : k=i
      · subst k; rfl
      · exact (cond k i (by simpa [one_apply,hik] using h)).symm

theorem reframe (j : J) (F : StartAxes) (s t : Lab) :
    CDPath j F s t 1 (frameCost s t) := of_id (CPath.reframe ..)

end CDPath

theorem invocation_path (j : J) (F : StartAxes) :
    CDPath j F (bp j) (bend j) (1+eXY) (invocationCost j) := by
  have h0 := CDPath.paired zero_JJ (sync0 j F) |>.2
  have h1 := CDPath.paired zero_RR (sync1 j F) |>.2
  have h2 := CDPath.paired zero_VV (sync2 j F) |>.1
  have h3 := CDPath.paired zero_GG (sync3 j F) |>.1
  have h4 := CDPath.paired zero_RR (sync4 j F) |>.1
  have h5 := CDPath.paired zero_JJ (sync5 j F) |>.1
  have h6 := CDPath.paired zero_GG (sync6 j F) |>.2
  have h7 := CDPath.paired zero_VV (sync7 j F) |>.2
  have H0 := (CDPath.reframe j F (bp j) (b0 j)).trans h0
  have H1 := H0.trans (CDPath.reframe j F (b0 j) (b1 j)) |>.trans h1
  have H2 := H1.trans (CDPath.reframe j F (b1 j) (b2 j)) |>.trans h2
  have H3 := H2.trans (CDPath.reframe j F (b2 j) (b3 j)) |>.trans h3
  have H4 := H3.trans (CDPath.reframe j F (b3 j) (b4 j)) |>.trans h4
  have H5 := H4.trans (CDPath.reframe j F (b4 j) (b5 j)) |>.trans h5
  have H6 := H5.trans (CDPath.reframe j F (b5 j) (b6 j)) |>.trans h6
  have H7 := H6.trans (CDPath.reframe j F (b6 j) (b7 j)) |>.trans h7
  have Hl := H7.trans (CDPath.reframe j F (b7 j) (bend j))
  rw [← net_eq,net]
  simpa only [invocationCost,← Matrix.mul_assoc,mul_one,one_mul,add_zero] using Hl

theorem invocation (j : J) (F : StartAxes) :
    CPath (basisBox j F) (bp j) (bend j)
      OriginalGroupedPricedSharedNetwork.forward (invocationCost j) ∧
    CPath (basisBox j F) (bp j) (bend j)
      OriginalGroupedPricedSharedNetwork.backward (invocationCost j) := by
  obtain ⟨N,hN,H,G⟩ := invocation_path j F
  have h : N=1-eXY := by
    calc
      N=((1-eXY)*(1+eXY))*N := by rw [inv_one_sub zero_XX,one_mul]
      _=_ := by rw [Matrix.mul_assoc,hN,mul_one]
  subst N
  exact ⟨OriginalGroupedPricedSharedNetwork.ap_f ▸ H,
    OriginalGroupedPricedSharedNetwork.ap_b ▸ G⟩

/-- The finite native stage, including every original side and center role.
Its cost is the sum of its actual invocation words, not an external census. -/
theorem stage (rev : Bool) (j : J) :
    CPath bases (border j.val) (border (j.val+1)) (stageOp rev)
      (fun c => (Fintype.card (Other j):ℝ)*invocationCost j c) := by
  have hd : (fun c => (Fintype.card (Other j):ℝ)*invocationCost j c) =
      (fun c => ∑ _ : Other j,invocationCost j c) := by
    funext c
    rw [sum_const,card_univ,nsmul_eq_mul]
  rw [hd]
  let h := fun _ : Other j =>
    if rev then OriginalGroupedPricedSharedNetwork.backward
      else OriginalGroupedPricedSharedNetwork.forward
  apply CPath.parallel (position j) (pos_dis j) bases (h:=h)
  · intro i
    rw [bases_local,border_bp,border_end]
    cases rev
    · exact (invocation j (axes j i)).1
    · exact (invocation j (axes j i)).2
  · intro i x
    funext r
    rcases r with ((r|r)|(r|r)) <;> cases rev <;> rfl
  · rintro x ((k|k)|r) hr
    · exfalso; specialize hr (omitJ j k); apply hr; rw [cover_iff]
      exact ⟨bx (k j),congr_arg gx (locate_omit ..)⟩
    · exfalso; specialize hr (omitJ j k); apply hr; rw [cover_iff]
      exact ⟨byy (k j),congr_arg gy (locate_omit ..)⟩
    · rfl
  · rintro ((k|k)|(⟨i,p,a⟩|r)) hr
    · exfalso; specialize hr (omitJ j k); apply hr; rw [cover_iff]
      exact ⟨bx (k j),congr_arg gx (locate_omit ..)⟩
    · exfalso; specialize hr (omitJ j k); apply hr; rw [cover_iff]
      exact ⟨byy (k j),congr_arg gy (locate_omit ..)⟩
    · by_cases ig : i=j
      · subst i; exfalso; specialize hr p; apply hr; rw [cover_iff]
        exact ⟨.inr a,rfl⟩
      · change (if i.val<j.val then univ else ∅)=
          (if i.val<j.val+1 then univ else ∅)
        have h : i.val≠j.val := fun h => ig (Fin.ext h)
        simp only [show (i.val<j.val+1) ↔ (i.val<j.val) from (by omega)]
    · rfl

def nativeCost (c : ℕ → ℝ) : ℝ :=
  (Fintype.card (Other (0:J)):ℝ)*invocationCost 0 c +
  (Fintype.card (Other (1:J)):ℝ)*invocationCost 1 c +
  (Fintype.card (Other (2:J)):ℝ)*invocationCost 2 c +
  frameCost (border 3) sink c

theorem all_stages : CPath bases (border 0) sink exchange nativeCost := by
  have h := ((stage false 0).trans (stage true 1)).trans (stage false 2)
  change CPath _ (border 0) (border 3)
    (stageOp false ∘ stageOp true ∘ stageOp false) _ at h
  have g := h.trans (CPath.reframe bases (border 3) sink)
  have he : id ∘ (stageOp false ∘ stageOp true ∘ stageOp false)=exchange := by
    funext x r
    rcases r with (k|k)|r <;> simp [Function.comp_apply,stageOp,exchange,gx,gy]
  simpa only [he,nativeCost] using g

/-- One concrete native word has the exact all-original-output semantics
and the complete actual-frame cost functional simultaneously. -/
theorem certificate :
    ∃ p : OriginalGroupedFrameWords.Word Blocks Role,
      (∀ c : ℕ → ℝ, c 0=0 → wordCost p c=nativeCost c) ∧
      ∀ f (x : Data Blocks Role f),
        OriginalGroupedFrameWords.walk bases f p x=
          multiAct f (fun _ => kernel Blocks) x := by
  obtain ⟨p,hp,he⟩ := all_stages
  refine ⟨p++[.translate correction,.localM recoverM],?_,?_⟩
  · intro c hc
    rw [wordCost_append,hp c hc]
    simp [wordCost,moveCost]
  · intro f x
    obtain ⟨y,rfl⟩ := framed_surj bases (border 0) f x
    rw [OriginalGroupedFrameWords.walk_append,he]
    simp only [OriginalGroupedFrameWords.walk,List.foldl_cons,List.foldl_nil,
      OriginalGroupedFrameWords.Move.go,recover_eq]
    exact netEffect f y

/-- The recurrence moment is the literal retained native-frame cost of the
same correct word.  No favorable histogram is assumed in this statement. -/
theorem native_word_moment :
    ∃ p : OriginalGroupedFrameWords.Word Blocks Role,
      (∀ u a : ℕ, ∀ z : ℝ,
        OriginalGroupedWordProfile.moment p u a z=nativeCost (momentCost u a z)) ∧
      ∀ f (x : Data Blocks Role f),
        OriginalGroupedFrameWords.walk bases f p x=
          multiAct f (fun _ => kernel Blocks) x := by
  obtain ⟨p,hp,he⟩ := certificate
  refine ⟨p,?_,he⟩
  intro u a z
  exact (moment_eq_wordCost p u a z).trans (hp (momentCost u a z) (by rfl))

theorem side_non_neighbors_card :
    Fintype.card {s : Side // ¬neighbor s.1 s.2}=4279240 := by
  rw [Fintype.card_subtype_compl]
  rw [OriginalGroupedNeighborCount.neighbor_side_card]
  simp only [Fintype.card_prod,num_trip] <;> norm_num

theorem card_spare : Fintype.card Spare=310637221254224 := by
  change Fintype.card (Fin (tower-nrRoles))=310637221254224
  rw [Fintype.card_fin]
  norm_num [tower,nrRoles]

/-- Cardinality reduction for a literal native stamp.  This partitions the
actual side-role type by the proved graph predicate, without evaluating its
millions of inhabitants. -/
theorem stamp_cost (x y s z d x' y' s' z' d' : Mask) (c : ℕ → ℝ) :
    frameCost (stamp x y s z d) (stamp x' y' s' z' d') c =
      4060*c (changeSize x x')+4060*c (changeSize y y')+
      12204360*c (changeSize s s')+4279240*c (changeSize d d')+
      33*c (changeSize z z') := by
  have hs : (∑ a : Side,
      c (changeSize (if neighbor a.1 a.2 then s else d)
        (if neighbor a.1 a.2 then s' else d'))) =
        12204360*c (changeSize s s')+4279240*c (changeSize d d') := by
    rw [← Fintype.sum_subtype_add_sum_subtype
      (fun a : Side => neighbor a.1 a.2)]
    have ht (a : OriginalGroupedNeighborCount.NeighborSide) :
        c (changeSize (if neighbor a.val.1 a.val.2 then s else d)
          (if neighbor a.val.1 a.val.2 then s' else d'))=c (changeSize s s') := by
      rw [if_pos a.property,if_pos a.property]
    have hf (a : {a : Side // ¬neighbor a.1 a.2}) :
        c (changeSize (if neighbor a.val.1 a.val.2 then s else d)
          (if neighbor a.val.1 a.val.2 then s' else d'))=c (changeSize d d') := by
      rw [if_neg a.property,if_neg a.property]
    simp_rw [ht,hf]
    simp only [sum_const,card_univ,nsmul_eq_mul]
    rw [OriginalGroupedNeighborCount.neighbor_side_card,side_non_neighbors_card]
    norm_num
  unfold frameCost
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp only [stamp]
  rw [hs]
  simp only [sum_const,card_univ,nsmul_eq_mul,num_trip,
    OriginalGroupedNativeInventory.card_center]
  ring

def IsSpare : Role → Prop
  | .inr (.inr _) => True
  | _ => False

instance isSpareDec : DecidablePred IsSpare := by
  intro r
  rcases r with a|a
  · exact isFalse id
  · rcases a with a|a
    · exact isFalse id
    · exact isTrue trivial

def spareEquiv : {r : Role // IsSpare r} ≃ Spare where
  toFun := by
    rintro ⟨r,hr⟩
    rcases r with a|a
    · exact False.elim hr
    · rcases a with a|a
      · exact False.elim hr
      · exact a
  invFun r := ⟨.inr (.inr r),trivial⟩
  left_inv := by
    rintro ⟨r,hr⟩
    rcases r with a|a
    · exact False.elim hr
    · rcases a with a|a
      · exact False.elim hr
      · rfl
  right_inv r := rfl

theorem closing_cost (c : ℕ → ℝ) (hc : c 0=0) :
    frameCost (border 3) sink c =
      (Fintype.card Spare:ℝ)*c 32768 := by
  have hh (r : Role) : c (changeSize (border 3 r) (sink r)) =
      if IsSpare r then c 32768 else 0 := by
    rcases r with ((k|k)|(⟨j,p,a⟩|r))
    · simp [IsSpare,border,sink,region_full,rim,changeSize,hc]
    · simp [IsSpare,border,sink,region_full,rim,changeSize,hc]
    · simp [IsSpare,border,sink,j.isLt,changeSize,hc]
    · simp [IsSpare,border,sink,changeSize,OriginalGroupedMaskCards.card_blocks]
  unfold frameCost
  simp_rw [hh]
  rw [indicator_sum,Fintype.card_congr spareEquiv]

theorem changeSize_of_subset {s t : Finset α} (h : s⊆t) :
    changeSize s t=t.card-s.card := by
  simp [changeSize,sdiff_eq_empty_iff_subset.mpr h,card_sdiff_of_subset h]

theorem changeSize_symm (s t : Finset α) : changeSize s t=changeSize t s := by
  unfold changeSize
  omega

theorem changeSize_self (s : Finset α) : changeSize s s=0 := by
  simp [changeSize]

theorem changeSize_empty_left (s : Finset α) : changeSize ∅ s=s.card := by
  simp [changeSize]

theorem invocationCost_eq (j : J) (c : ℕ → ℝ) (hc : c 0=0) :
    invocationCost j c =
      8120*c (OriginalGroupedMaskCards.stageRanks j 0)+
      8120*c (OriginalGroupedMaskCards.stageRanks j 1)+
      33*c (OriginalGroupedMaskCards.stageRanks j 2)+
      99*c (OriginalGroupedMaskCards.stageRanks j 3)+
      33*c (OriginalGroupedMaskCards.stageRanks j 4)+
      12204360*(c (OriginalGroupedMaskCards.stageRanks j 5)+
        c (OriginalGroupedMaskCards.stageRanks j 6)+
        c (OriginalGroupedMaskCards.stageRanks j 7)+
        c (OriginalGroupedMaskCards.stageRanks j 8)+
        c (OriginalGroupedMaskCards.stageRanks j 9))+
      4279240*c 32768 := by
  have hxb : xstep j 0⊆big j := by
    intro x hx
    exact (in_big j x).mpr ((in_xstep j 0 x).mp hx).1
  have hbb : belt j⊆big j := by
    intro x hx
    exact (in_big j x).mpr ((in_belt j x).mp hx).1
  have hby (slot : H) : belt j⊆ystep j slot := by
    intro x hx
    obtain ⟨hf,hp⟩ := (in_belt j x).mp hx
    exact (in_ystep j slot x).mpr ⟨hf,Or.inl hp⟩
  have hyb (slot : H) : ystep j slot⊆big j := by
    intro x hx
    exact (in_big j x).mpr ((in_ystep j slot x).mp hx).1
  have h0 : changeSize (xstart j 0) (xstep j 0)=
      OriginalGroupedMaskCards.stageRanks j 0 := by
    rw [changeSize_of_subset (OriginalGroupedMaskCards.xstart_subset_xstep j 0)]
    change (xstep j 0).card-(xstart j 0).card=((xstep j 0)\xstart j 0).card
    exact (card_sdiff_of_subset (OriginalGroupedMaskCards.xstart_subset_xstep j 0)).symm
  have h0y : changeSize (ystart j 0) (belt j)=
      OriginalGroupedMaskCards.stageRanks j 0 := by
    rw [changeSize_of_subset (OriginalGroupedMaskCards.ystart_subset_belt j 0),
      OriginalGroupedMaskCards.stageRanks_eq,
      OriginalGroupedMaskCards.card_belt,OriginalGroupedMaskCards.card_ystart]
    fin_cases j <;> norm_num [OriginalGroupedResidualCertificate.edgeRank]
  have h1 : changeSize (xstep j 0) (big j)=
      OriginalGroupedMaskCards.stageRanks j 1 := by
    rw [changeSize_of_subset hxb]
    change (big j).card-(xstep j 0).card=((big j)\xstep j 0).card
    exact (card_sdiff_of_subset hxb).symm
  have h1y : changeSize (belt j) (ystep j 0)=
      OriginalGroupedMaskCards.stageRanks j 1 := by
    rw [changeSize_of_subset (hby 0),OriginalGroupedMaskCards.stageRanks_eq,
      OriginalGroupedMaskCards.card_belt,OriginalGroupedMaskCards.card_ystep]
    fin_cases j <;> norm_num [OriginalGroupedResidualCertificate.edgeRank]
  have h2 : changeSize ∅ (belt j)=OriginalGroupedMaskCards.stageRanks j 2 := by
    rw [changeSize_empty_left]
    rfl
  have h3 : changeSize (belt j) (big j)=OriginalGroupedMaskCards.stageRanks j 3 := by
    rw [changeSize_of_subset hbb]
    change (big j).card-(belt j).card=((big j)\belt j).card
    exact (card_sdiff_of_subset hbb).symm
  have h3r : changeSize (big j) (belt j)=OriginalGroupedMaskCards.stageRanks j 3 := by
    rw [changeSize_symm]
    exact h3
  have h4 : changeSize (big j) univ=OriginalGroupedMaskCards.stageRanks j 4 := by
    rw [changeSize_of_subset (subset_univ _)]
    change univ.card-(big j).card=(univ\big j).card
    exact (card_sdiff_of_subset (subset_univ (big j))).symm
  have h5 : changeSize ∅ (ystart j 1)=OriginalGroupedMaskCards.stageRanks j 5 := by
    rw [changeSize_empty_left]
    rfl
  have h6 : changeSize (ystart j 1) (xstep j 0)=
      OriginalGroupedMaskCards.stageRanks j 6 := by
    rw [changeSize_of_subset (OriginalGroupedMaskCards.ystart_one_subset_xstep_zero j)]
    change (xstep j 0).card-(ystart j 1).card=((xstep j 0)\ystart j 1).card
    exact (card_sdiff_of_subset
      (OriginalGroupedMaskCards.ystart_one_subset_xstep_zero j)).symm
  have h7 : changeSize (xstep j 0) (ystep j 1)=
      OriginalGroupedMaskCards.stageRanks j 7 := by
    rw [changeSize_of_subset (OriginalGroupedMaskCards.xstep_zero_subset_ystep_one j)]
    change (ystep j 1).card-(xstep j 0).card=((ystep j 1)\xstep j 0).card
    exact (card_sdiff_of_subset
      (OriginalGroupedMaskCards.xstep_zero_subset_ystep_one j)).symm
  have h8 : changeSize (ystep j 1) (big j)=OriginalGroupedMaskCards.stageRanks j 8 := by
    rw [changeSize_of_subset (hyb 1)]
    change (big j).card-(ystep j 1).card=((big j)\ystep j 1).card
    exact (card_sdiff_of_subset (hyb 1)).symm
  have h9 : changeSize (big j) univ=OriginalGroupedMaskCards.stageRanks j 9 := by
    exact h4
  have h49 : OriginalGroupedMaskCards.stageRanks j 9=
      OriginalGroupedMaskCards.stageRanks j 4 := rfl
  have hfull : changeSize (∅:Mask) univ=32768 := by
    rw [changeSize_empty_left,card_univ,OriginalGroupedMaskCards.card_blocks]
  unfold invocationCost
  simp only [bp,b0,b1,b2,b3,b4,b5,b6,b7,bend,stamp_cost]
  simp only [h0,h0y,h1,h1y,h2,h3,h3r,h4,h5,h6,h7,h8,h9,hfull,
    h49,changeSize_self,hc,mul_zero,add_zero,zero_add]
  ring

private theorem vec10_nat (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : ℕ) (i : Fin 10) :
    ![a0,a1,a2,a3,a4,a5,a6,a7,a8,a9] i =
      match i.val with
      | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3 | 4 => a4
      | 5 => a5 | 6 => a6 | 7 => a7 | 8 => a8 | _ => a9 := by
  fin_cases i <;> rfl

private theorem vec12_nat (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : ℕ)
    (i : Fin 12) :
    ![a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11] i =
      match i.val with
      | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3 | 4 => a4 | 5 => a5
      | 6 => a6 | 7 => a7 | 8 => a8 | 9 => a9 | 10 => a10 | _ => a11 := by
  fin_cases i <;> rfl

/-- The finite 3-by-10 geometry is now evaluated for the SAME emitted-word
cost functional.  All nonneighbor helpers and all original Spare roles
appear as full-order calls in the padding term. -/
theorem nativeCost_moment_eq (z : ℝ) :
    nativeCost (momentCost 32768 50 z)=
      OriginalGroupedResidualCertificate.paddedMoment32 z := by
  have hc : momentCost 32768 50 z 0=0 := by simp [momentCost]
  unfold nativeCost
  rw [closing_cost _ hc,invocationCost_eq 0 _ hc,
    invocationCost_eq 1 _ hc,invocationCost_eq 2 _ hc]
  simp only [card_other,card_spare,OriginalGroupedMaskCards.stageRanks_eq]
  simp only [OriginalGroupedResidualCertificate.edgeRank,
    OriginalGroupedResidualCertificate.paddedMoment32,
    OriginalGroupedResidualCertificate.padding32,
    OriginalGroupedResidualCertificate.paddedWeight32,
    OriginalGroupedResidualCertificate.point32,
    OriginalGroupedResidualCertificate.moment,
    OriginalGroupedResidualCertificate.rho32,
    OriginalGroupedResidualCertificate.count32,
    OriginalGroupedResidualCertificate.roles32,
    OriginalGroupedResidualCertificate.order32,
    OriginalGroupedResidualCertificate.padded32,
    Fin.sum_univ_succ,Fin.sum_univ_zero]
  simp only [vec10_nat,vec12_nat]
  norm_num [momentCost] <;> ring

/-- The stronger grouped exponent is attached to the very word which
preserves every arbitrary complex input and original auxiliary output. -/
theorem native_word_alpha32 :
    ∃ p : OriginalGroupedFrameWords.Word Blocks Role,
      OriginalGroupedWordProfile.moment p mcol 50
        OriginalGroupedResidualCertificate.alpha32<1 ∧
      ∀ f (x : Data Blocks Role f),
        OriginalGroupedFrameWords.walk bases f p x=
          multiAct f (fun _ => kernel Blocks) x := by
  obtain ⟨p,hp,he⟩ := native_word_moment
  refine ⟨p,?_,he⟩
  rw [hp]
  change nativeCost (momentCost 32768 50 OriginalGroupedResidualCertificate.alpha32)<1
  rw [nativeCost_moment_eq]
  exact OriginalGroupedResidualCertificate.paddedMoment32_alpha32_lt

end
end FourierSchur.OriginalGroupedCensusBridge
