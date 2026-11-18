import vendor.OpenAIUniformFourierBundle

/-! The shared network with full frame changes retained before compilation.
These are finite operator specifications on arbitrary complex data, not
free dense-matrix instructions. Each `frames` token must be compiled by
the paid whole-residual RAM layer; local maps and translations also pay.
The original expanded directional word is not substituted as a fallback.
-/
namespace FourierSchur.OriginalGroupedFrameWords

open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.Cluster Matrix Finset
noncomputable section

inductive Move (α ρ : Type*)
  | localM (M : Matrix ρ ρ ℚ)
  | frames (s t : ρ → Finset α)
  | translate (z : ρ → Space α)

abbrev Word (α ρ : Type*) := List (Move α ρ)

section
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ] [Fintype σ] [DecidableEq σ]

def Move.go (A : ρ → OBase α) (f : ℕ) : Move α ρ → Data α ρ f → Data α ρ f
  | .localM M => point f (actPoint M)
  | .frames s t => multiAct f (fun r => frame (A r) (t r) * unframe (A r) (s r))
  | .translate z => multiAct f (fun r => shift (z r))

def walk (A : ρ → OBase α) (f : ℕ) (p : Word α ρ) (x : Data α ρ f) :=
  p.foldl (fun y m => m.go A f y) x

theorem walk_append (A : ρ → OBase α) (f : ℕ) (p q : Word α ρ) (x : Data α ρ f) :
    walk A f (p++q) x = walk A f q (walk A f p x) := by simp [walk]

def Path (A : ρ → OBase α) (s t : ρ → Finset α)
    (g : (ρ → ℂ) → (ρ → ℂ)) : Prop :=
  ∃ p : Word α ρ, ∀ f x,
    walk A f p (withFrame A s f x) = withFrame A t f (point f g x)

namespace Path
variable {A : ρ → OBase α} {s t u : ρ → Finset α}

theorem refl : Path A s s id := by refine ⟨[],?_⟩; intro f x; rfl

theorem trans {g h} (a : Path A s t g) (b : Path A t u h) :
    Path A s u (h ∘ g) := by
  obtain ⟨p,ap⟩ := a
  obtain ⟨q,aq⟩ := b
  refine ⟨p++q,?_⟩
  intro f x
  rw [walk_append,ap,aq]
  rfl

/-- A complete frame change is one retained compiler request per role.
Its live coefficients are not evaluated by a table lookup. -/
theorem reframe (A : ρ → OBase α) (s t : ρ → Finset α) : Path A s t id := by
  refine ⟨[.frames s t],?_⟩
  intro f x
  funext r
  simp [walk,Move.go,withFrame,multiAct,matAct_mul,Matrix.mul_assoc,unframe_left]
  rfl

theorem gate (M : Matrix ρ ρ ℚ)
    (cond : ∀ i j, M i j ≠ 0 → frame (A i) (s i) = frame (A j) (s j)) :
    Path A s s (actPoint M) := by
  refine ⟨[.localM M],?_⟩
  intro f x
  let T (r : ρ) := digitProd
    (fun _ : Fin f => frame (A r) (s r))
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

end Path

def extend {β : Type*} (e : ρ ↪ σ) (zero : β) (v : ρ → β) (r : σ) : β :=
  if h : ∃ i, e i=r then v (Classical.choose h) else zero

@[simp] theorem extend_on {β : Type*} (e : ρ ↪ σ) (zero : β) (v : ρ → β) (i : ρ) :
    extend e zero v (e i) = v i := by
  have h : ∃ j, e j=e i := ⟨i,rfl⟩
  rw [extend,dif_pos h]
  rw [e.injective (Classical.choose_spec h)]

theorem extend_off {β : Type*} (e : ρ ↪ σ) (zero : β) (v : ρ → β)
    {r : σ} (h : r ∉ covered e) : extend e zero v r=zero := by
  have hn : ¬∃ i, e i=r := fun g => h ((cover_iff e r).2 g)
  simp [extend,hn]

def Move.over (e : ρ ↪ σ) : Move α ρ → Move α σ
  | .localM M => .localM (wide e M)
  | .frames s t => .frames (extend e ∅ s) (extend e ∅ t)
  | .translate z => .translate (extend e 0 z)

theorem go_over (e : ρ ↪ σ) (A : σ → OBase α) (m : Move α ρ)
    (f : ℕ) (x : Data α σ f) :
    (m.over e |>.go A f x) ∘ e = m.go (A∘e) f (x∘e) := by
  funext i j
  cases m with
  | localM M => exact wide_in e M i (fun r => x r j)
  | frames s t => simp [Move.over,Move.go,multiAct,Function.comp_def]
  | translate z => simp [Move.over,Move.go,multiAct,Function.comp_def]

theorem go_out (e : ρ ↪ σ) (A : σ → OBase α) (m : Move α ρ) (f : ℕ)
    (x : Data α σ f) {r : σ} (h : r ∉ covered e) :
    (m.over e |>.go A f x) r=x r := by
  cases m with
  | localM M => funext j; exact wide_out e M (fun r => x r j) h
  | frames s t =>
    simp [Move.over,Move.go,multiAct,extend_off e _ _ h,
      unframe,OBase.proj,wrap_one,matAct_one]
  | translate z => simp [Move.over,Move.go,multiAct,extend_off e _ _ h,shift_zero]

theorem walk_over (e : ρ ↪ σ) (A : σ → OBase α) (p : Word α ρ) (f : ℕ)
    (x : Data α σ f) :
    walk A f (p.map (Move.over e)) x ∘ e = walk (A∘e) f p (x∘e) := by
  induction p generalizing x with
  | nil => rfl
  | cons m p ih =>
    change walk _ _ _ _ ∘ e = walk _ f p (m.go (A∘e) f (x∘e))
    rw [← go_over]
    exact ih _

theorem walk_out (e : ρ ↪ σ) (A : σ → OBase α) (p : Word α ρ) (f : ℕ)
    (x : Data α σ f) {r : σ} (h : r ∉ covered e) :
    walk A f (p.map (Move.over e)) x r=x r := by
  induction p generalizing x with
  | nil => rfl
  | cons m p ih => exact (ih _).trans (go_out e A m f x h)

namespace Path

theorem lift (e : ρ ↪ σ) (A : σ → OBase α) {s t : σ → Finset α}
    {g : (σ→ℂ)→(σ→ℂ)} {h : (ρ→ℂ)→(ρ→ℂ)}
    (q : Path (A∘e) (s∘e) (t∘e) h)
    (hin : ∀ x, (g x)∘e=h (x∘e)) (hout : ∀ x r, r∉covered e → g x r=x r)
    (he : ∀ r, r∉covered e → s r=t r) : Path A s t g := by
  obtain ⟨p,ha⟩ := q
  refine ⟨p.map (Move.over e),?_⟩
  intro f x
  have frame_cont (s : σ → Finset α) (x : Data α σ f) :
      withFrame A s f x ∘ e=withFrame (A∘e) (s∘e) f (x∘e) := rfl
  have point_cont : point f g x ∘ e=point f h (x∘e) := by
    funext i j
    exact congr_fun (hin _) i
  funext r
  by_cases hr : r ∈ covered e
  · obtain ⟨j,rfl⟩ := (cover_iff ..).mp hr
    exact congr_fun (show walk A f _ _ ∘ e=withFrame A t f _ ∘ e by
      rw [walk_over,frame_cont,ha,frame_cont,point_cont]) j
  · rw [walk_out e A p _ _ hr]
    unfold withFrame multiAct
    simp only [he r hr]
    apply congrArg
    funext j
    exact (hout (fun r => x r j) r hr).symm

theorem parallel {J : Type*} [Fintype J] [DecidableEq J] (e : J → ρ ↪ σ)
    (dis : ∀ i j, i≠j → ∀ r∈covered (e i), r∉covered (e j))
    (A : σ → OBase α) {s t : σ → Finset α}
    {g : (σ→ℂ)→(σ→ℂ)} {h : J → (ρ→ℂ)→(ρ→ℂ)}
    (q : ∀ i, Path (A∘e i) (s∘e i) (t∘e i) (h i))
    (hin : ∀ i x, (g x)∘e i=h i (x∘e i))
    (hout : ∀ x r, (∀ i, r∉covered (e i)) → g x r=x r)
    (he : ∀ r, (∀ i, r∉covered (e i)) → s r=t r) : Path A s t g := by
  let u (j : Finset J) := j.biUnion fun i => covered (e i)
  let l (j : Finset J) (r : σ) := if r∈u j then t r else s r
  let k (j : Finset J) (x : σ→ℂ) (r : σ) := if r∈u j then g x r else x r
  have hh (j : Finset J) : Path A s (l j) (k j) := by
    induction j using Finset.induction with
    | empty => simpa only [k,l,u,biUnion_empty,notMem_empty,ite_false] using
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
      have gg : Path A (l j) (l (insert i j)) fn := by
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
      rw [← cmp]
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
end
end FourierSchur.OriginalGroupedFrameWords
