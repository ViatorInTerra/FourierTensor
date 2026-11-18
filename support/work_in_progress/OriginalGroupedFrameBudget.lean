import work_in_progress.OriginalGroupedFrameWords

/-! Exact first-moment inventory of a grouped frame word. A whole residual
is retained as one kernel request; its dimension is charged here. The
nonrecursive work of points, translations and routing is paid separately
by the RAM compiler. Zero recursive moment does not mean zero RAM work.
-/
namespace FourierSchur.OriginalGroupedFrameBudget
open OAI.PowerSaving OAI.PowerSaving.Binary Matrix Finset
open OriginalGroupedFrameWords
noncomputable section
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ] [Fintype σ] [DecidableEq σ]

def changeSize (s t : Finset α) : ℕ := (s\t).card+(t\s).card

theorem change_mass (s t : Finset α) :
    changeSize s t+s.card=t.card+2*(s\t).card := by
  have hs := card_sdiff_add_card_inter s t
  have ht := card_sdiff_add_card_inter t s
  rw [inter_comm t s] at ht
  unfold changeSize
  omega

def moveMoment : OriginalGroupedFrameWords.Move α ρ → ℕ
  | .frames s t => ∑ r, changeSize (s r) (t r)
  | _ => 0

def firstMoment (p : Word α ρ) : ℕ := (p.map moveMoment).sum

theorem firstMoment_append (p q : Word α ρ) :
    firstMoment (p++q)=firstMoment p+firstMoment q := by simp [firstMoment]

theorem moveMoment_over (e : ρ ↪ σ) (m : OriginalGroupedFrameWords.Move α ρ) :
    moveMoment (m.over e)=moveMoment m := by
  cases m with
  | localM M => rfl
  | translate z => rfl
  | frames s t =>
    change (∑ r, changeSize (extend e ∅ s r) (extend e ∅ t r)) =
      ∑ r, changeSize (s r) (t r)
    rw [← sum_add_sum_compl (covered e)]
    have hz : ∑ r∈(covered e)ᶜ,
        changeSize (extend e ∅ s r) (extend e ∅ t r)=0 := by
      apply sum_eq_zero
      intro r hr
      have h := mem_compl.mp hr
      simp [extend_off e _ _ h,changeSize]
    rw [hz,Nat.add_zero,covered,sum_map]
    simp

theorem firstMoment_over (e : ρ ↪ σ) (p : Word α ρ) :
    firstMoment (p.map (OriginalGroupedFrameWords.Move.over e))=firstMoment p := by
  simp [firstMoment,List.map_map,Function.comp_def,moveMoment_over]

def Path (A : ρ → OBase α) (s t : ρ → Finset α)
    (g : (ρ→ℂ)→(ρ→ℂ)) (d : ℕ) : Prop :=
  ∃ p : Word α ρ, firstMoment p+mass s=mass t+2*d ∧
    ∀ f x, OriginalGroupedFrameWords.walk A f p (withFrame A s f x)=
      withFrame A t f (point f g x)

namespace Path
variable {A : ρ → OBase α} {s t u : ρ → Finset α}

theorem refl : Path A s s id 0 := by refine ⟨[],by simp [firstMoment],?_⟩; intro f x; rfl

theorem trans {g h i j} (a : Path A s t g i) (b : Path A t u h j) :
    Path A s u (h∘g) (i+j) := by
  obtain ⟨p,hp,ap⟩ := a
  obtain ⟨q,hq,aq⟩ := b
  refine ⟨p++q,by rw [firstMoment_append]; omega,?_⟩
  intro f x
  rw [OriginalGroupedFrameWords.walk_append,ap,aq]
  rfl

theorem reframe (A : ρ → OBase α) (s t : ρ → Finset α) : Path A s t id (loss s t) := by
  refine ⟨[.frames s t],?_,?_⟩
  · simp only [firstMoment,moveMoment,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      Nat.add_zero,mass,loss]
    rw [← sum_add_distrib,Finset.mul_sum,← sum_add_distrib]
    apply sum_congr rfl
    intro r hr
    exact change_mass (s r) (t r)
  · intro f x
    funext r
    simp [OriginalGroupedFrameWords.walk,OriginalGroupedFrameWords.Move.go,
      withFrame,multiAct,matAct_mul,Matrix.mul_assoc,unframe_left]
    rfl

theorem inc (A : ρ → OBase α) {s t : ρ → Finset α} (h : ∀ r, s r⊆t r) :
    Path A s t id 0 := by
  have hz : loss s t=0 := by simp [loss,sdiff_eq_empty_iff_subset.mpr (h _)]
  simpa [hz] using reframe A s t

theorem gate (M : Matrix ρ ρ ℚ)
    (cond : ∀ i j, M i j≠0 → frame (A i) (s i)=frame (A j) (s j)) :
    Path A s s (actPoint M) 0 := by
  refine ⟨[.localM M],by simp [firstMoment,moveMoment],?_⟩
  intro f x
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
    {g : (σ→ℂ)→(σ→ℂ)} {h : (ρ→ℂ)→(ρ→ℂ)} {d : ℕ}
    (q : Path (A∘e) (s∘e) (t∘e) h d)
    (hin : ∀ x, (g x)∘e=h (x∘e)) (hout : ∀ x r, r∉covered e → g x r=x r)
    (he : ∀ r, r∉covered e → s r=t r) : Path A s t g d := by
  obtain ⟨p,hp,ha⟩ := q
  refine ⟨p.map (OriginalGroupedFrameWords.Move.over e),?_,?_⟩
  · have hm (s : σ → Finset α) :
        mass s=mass (s∘e)+∑ r∈(covered e)ᶜ, (s r).card := by
      unfold mass
      rw [← sum_add_sum_compl (covered e)]
      rw [covered,sum_map]
      rfl
    have hh : ∑ r∈(covered e)ᶜ, (s r).card=∑ r∈(covered e)ᶜ, (t r).card := by
      apply sum_congr rfl
      intro r hr
      rw [he r (mem_compl.mp hr)]
    rw [firstMoment_over,hm,hm,hh]
    omega
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

theorem parallel {J : Type*} [Fintype J] [DecidableEq J] (e : J → ρ ↪ σ)
    (dis : ∀ i j, i≠j → ∀ r∈covered (e i), r∉covered (e j))
    (A : σ → OBase α) {s t : σ → Finset α} {d : J → ℕ}
    {g : (σ→ℂ)→(σ→ℂ)} {h : J → (ρ→ℂ)→(ρ→ℂ)}
    (q : ∀ i, Path (A∘e i) (s∘e i) (t∘e i) (h i) (d i))
    (hin : ∀ i x, (g x)∘e i=h i (x∘e i))
    (hout : ∀ x r, (∀ i, r∉covered (e i)) → g x r=x r)
    (he : ∀ r, (∀ i, r∉covered (e i)) → s r=t r) : Path A s t g (∑ i,d i) := by
  let u (j : Finset J) := j.biUnion fun i => covered (e i)
  let l (j : Finset J) (r : σ) := if r∈u j then t r else s r
  let k (j : Finset J) (x : σ→ℂ) (r : σ) := if r∈u j then g x r else x r
  have hh (j : Finset J) : Path A s (l j) (k j) (∑ i∈j,d i) := by
    induction j using Finset.induction with
    | empty =>
      simpa only [k,l,u,biUnion_empty,notMem_empty,ite_false,sum_empty] using
        (Path.refl (A:=A) (s:=s))
    | insert i j hi ih =>
      have hiu (r) (hr : r∈covered (e i)) : r∉u j := by
        intro hg
        obtain ⟨w,hw,he'⟩ := mem_biUnion.mp hg
        have hw' : i≠w := by intro H; subst w; exact hi hw
        exact dis _ _ hw' r hr he'
      have hui (r) : r∈u (insert i j) ↔ r∈covered (e i) ∨ r∈u j := by simp [u]
      let fn (x : σ→ℂ) (r : σ) := if r∈covered (e i) then g x r else x r
      have compi (x) : fn x∘e i=h i (x∘e i) := by
        rw [← hin]
        funext r; simp [fn,covered]
      have gg : Path A (l j) (l (insert i j)) fn (d i) := by
        apply Path.lift (e i) A (h:=h i) _ compi
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
          have H := congr_fun (show fn (k j x)∘e i=g x∘e i by rw [compi,eq,hin]) r
          exact H.trans (by simp [k,hui,hqr])
        · simp [Function.comp,k,fn,hui,hqr]
      rw [sum_insert hi,add_comm,← cmp]
      exact ih.trans gg
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

end Path
end
end FourierSchur.OriginalGroupedFrameBudget
