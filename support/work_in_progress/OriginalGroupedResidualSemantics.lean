import work_in_progress.OriginalGroupedResidualRAM
import work_in_progress.OriginalGroupedFrameFactorization

namespace OAI.PowerSaving.RAM.GroupedResidual
open OAI PowerSaving Binary Matrix Finset
noncomputable section

variable {α β γ : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

def columnSplit (e : ColumnRoute α β γ) : Space α ≃ (Space β × Space γ) where
  toFun x := (fun b => e.equiv x (.inl b),fun c => e.equiv x (.inr c))
  invFun x := e.equiv.symm (Sum.elim x.1 x.2)
  left_inv x := by
    change e.equiv.symm (Sum.elim _ _) = x
    have h : Sum.elim (fun b => e.equiv x (.inl b))
        (fun c => e.equiv x (.inr c)) = e.equiv x := by
      funext q; cases q <;> rfl
    rw [h]; exact e.equiv.symm_apply_apply x
  right_inv x := by
    apply Prod.ext <;> funext q <;> dsimp <;> rw [Equiv.apply_symm_apply] <;> rfl

def columnKernel (e : ColumnRoute α β γ) : CMat α := fun x y =>
  kernel β (columnSplit e x).1 (columnSplit e y).1 *
    (if (columnSplit e x).2=(columnSplit e y).2 then 1 else 0)

lemma dot_merge (A : OBase α) (j : (β ⊕ γ) ≃ α)
    (z : Space β) (w : Space γ) (ξ : Space α) :
    dot ((columnSplit (ColumnRoute.ofOBase A j)).symm (z,w)) ξ =
      dot z (columnSplit (ColumnRoute.ofOBase A j) ξ).1+
      dot w (columnSplit (ColumnRoute.ofOBase A j) ξ).2 := by
  change (∑ a, (∑ q : α, A.v q a * (Sum.elim z w) (j.symm q))*ξ a) = _
  simp_rw [sum_mul]
  rw [sum_comm,← Equiv.sum_comp j,Fintype.sum_sum_type]
  congr 1 <;> apply sum_congr rfl <;> intro q hq
  · simp only [Equiv.symm_apply_apply,Sum.elim_inl]
    change (∑ a, A.v (j (.inl q)) a * z q * ξ a) =
      z q * ∑ a, A.v (j (.inl q)) a * ξ a
    rw [mul_sum]; apply sum_congr rfl; intro a ha; ring
  · simp only [Equiv.symm_apply_apply,Sum.elim_inr]
    change (∑ a, A.v (j (.inr q)) a * w q * ξ a) =
      w q * ∑ a, A.v (j (.inr q)) a * ξ a
    rw [mul_sum]; apply sum_congr rfl; intro a ha; ring

lemma kernel_wal (β : Type*) [Fintype β] [DecidableEq β] :
    kernel β * wal β = wal β * diagonal (lum : Space β → ℂ) := by
  rw [← wrap_lum,wrap,Matrix.mul_assoc,wal_left]
  simp

lemma columnKernel_phase (A : OBase α) (j : (β ⊕ γ) ≃ α) :
    columnKernel (ColumnRoute.ofOBase A j) * wal α = wal α *
      diagonal (fun ξ => lum (columnSplit (ColumnRoute.ofOBase A j) ξ).1) := by
  let e := ColumnRoute.ofOBase A j
  let E := columnSplit e
  ext x ξ
  rw [Matrix.mul_apply,← Equiv.sum_comp E.symm,Fintype.sum_prod_type,
    Matrix.mul_diagonal]
  dsimp only [E,e]
  simp only [columnKernel,Equiv.apply_symm_apply]
  simp_rw [wal_apply,dot_merge A j,sign_add]
  simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul]
  simp only [Fintype.sum_ite_eq]
  have H := congr_fun (congr_fun (kernel_wal β) (E x).1) (E ξ).1
  rw [Matrix.mul_diagonal] at H
  simp only [Matrix.mul_apply,wal_apply] at H
  rw [show (∑ y : Space β, kernel β (E x).1 y *
      (sign (dot y (E ξ).1)*sign (dot (E x).2 (E ξ).2))) =
      (∑ y : Space β, kernel β (E x).1 y*sign (dot y (E ξ).1))*
        sign (dot (E x).2 (E ξ).2) by rw [sum_mul]; apply sum_congr rfl; intros; ring]
  rw [H]
  have HX := dot_merge A j (E x).1 (E x).2 ξ
  change dot (E.symm (E x)) ξ=dot (E x).1 (E ξ).1+dot (E x).2 (E ξ).2 at HX
  rw [Equiv.symm_apply_apply] at HX
  rw [HX,sign_add]
  ring

lemma columnKernel_subset (A : OBase α) (t : Finset α) :
    columnKernel (ColumnRoute.forSubset A t) =
      FourierSchur.OriginalGroupedFrameFactorization.forwardMask A t := by
  have H := columnKernel_phase A (ColumnRoute.subsetPartition t)
  have HP : (fun ξ => lum (columnSplit (ColumnRoute.forSubset A t) ξ).1) =
      FourierSchur.OriginalGroupedFrameFactorization.forwardPhase A t := by
    funext ξ
    change (∏ b : {i : α // i∈t}, tint (dot (A.v b.val) ξ)) =
      ∏ i ∈ t, tint (dot (A.v i) ξ)
    exact Finset.prod_coe_sort t (fun i => tint (dot (A.v i) ξ))
  change columnKernel (ColumnRoute.forSubset A t) * wal α = wal α *
    diagonal (fun ξ => lum (columnSplit (ColumnRoute.forSubset A t) ξ).1) at H
  rw [HP] at H
  exact (wrap_of _ _ H).symm

def skyRoute (e : ColumnRoute α β γ) (f : ℕ) :
    Sky α f ≃ (Sky β f × Sky γ f) where
  toFun x := (fun j => (columnSplit e (x j)).1,fun j => (columnSplit e (x j)).2)
  invFun x := fun j => (columnSplit e).symm (x.1 j,x.2 j)
  left_inv x := by funext j; exact (columnSplit e).symm_apply_apply (x j)
  right_inv x := by
    apply Prod.ext <;> funext j
    · exact congr_arg Prod.fst ((columnSplit e).apply_symm_apply (x.1 j,x.2 j))
    · exact congr_arg Prod.snd ((columnSplit e).apply_symm_apply (x.1 j,x.2 j))

lemma selected_kernel (Y : Layout β) (f : ℕ) (x y : Sky β f) :
    kernel (Fin (Y.n*f)) (selectedIndex Y f x) (selectedIndex Y f y) =
      digitProd (fun _ : Fin f => kernel β) x y := by
  simpa [selectedIndex,kernel,digitProd] using
    kernel_serial Y 0 f (k:=Y.n*f) (by omega)
      ((fun j => Fin.elim0 j),x) ((fun j => Fin.elim0 j),y)

lemma columnKernel_sky (e : ColumnRoute α β γ) (f : ℕ) (x y : Sky α f) :
    digitProd (fun _ : Fin f => columnKernel e) x y =
      digitProd (fun _ : Fin f => kernel β) (skyRoute e f x).1 (skyRoute e f y).1 *
        (if (skyRoute e f x).2=(skyRoute e f y).2 then 1 else 0) := by
  change (∏ j : Fin f, kernel β (columnSplit e (x j)).1 (columnSplit e (y j)).1 *
      (if (columnSplit e (x j)).2=(columnSplit e (y j)).2 then (1:ℂ) else 0)) = _
  rw [prod_mul_distrib,prod_delta]
  rfl

lemma matAct_columnKernel (e : ColumnRoute α β γ) (f : ℕ)
    (v : Sky α f → ℂ) (x : Sky α f) :
    matAct f (columnKernel e) v x =
      ∑ z : Sky β f, digitProd (fun _ : Fin f => kernel β) (skyRoute e f x).1 z *
        v ((skyRoute e f).symm (z,(skyRoute e f x).2)) := by
  change (∑ y, digitProd (fun _ : Fin f => columnKernel e) x y * v y) = _
  rw [← Equiv.sum_comp (skyRoute e f).symm,Fintype.sum_prod_type]
  simp_rw [columnKernel_sky]
  simp only [Equiv.apply_symm_apply]
  simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul,Fintype.sum_ite_eq]

/-- The executed complete selected tensor is exactly the tensor amplification
of the one-column partial kernel, with every outer spectator fixed. -/
lemma result_eq_matAct (e : ColumnRoute α β γ) (Y : Layout β) (r f : ℕ)
    (v : Grid α r f → ℂ) (g : Bits r) (x : Sky α f) :
    result e Y r f v (g,x) = matAct f (columnKernel e) (fun y => v (g,y)) x := by
  rw [matAct_columnKernel]
  change (∑ q : Bits (Y.n*f),
    kernel (Fin (Y.n*f))
      (selectedIndex Y f (skyRoute e f x).1) q *
      v ((split e Y r f).symm
        ((g,(skyRoute e f x).2),q))) = _
  rw [← Equiv.sum_comp (selectedIndex Y f)]
  simp_rw [selected_kernel]
  apply sum_congr rfl
  intro z hz
  congr 1
  change v (g,fun j => e.equiv.symm
    (Sum.elim ((selectedIndex Y f).symm (selectedIndex Y f z) j)
      ((skyRoute e f x).2 j))) = _
  simp only [Equiv.symm_apply_apply]
  rfl

/-- Leaf semantic bridge needed by the grouped frame compiler. It applies to
arbitrary complex input and retains every r-bit and complementary spectator. -/
theorem result_eq_forwardMask (A : OBase α) (t : Finset α)
    (Y : Layout {i : α // i∈t}) (r f : ℕ) (v : Grid α r f → ℂ)
    (g : Bits r) (x : Sky α f) :
    result (ColumnRoute.forSubset A t) Y r f v (g,x) =
      matAct f (FourierSchur.OriginalGroupedFrameFactorization.forwardMask A t)
        (fun y => v (g,y)) x := by
  rw [result_eq_matAct,columnKernel_subset]

theorem result_eq_forwardMask_fun (A : OBase α) (t : Finset α)
    (Y : Layout {i : α // i∈t}) (r f : ℕ) (v : Grid α r f → ℂ) :
    result (ColumnRoute.forSubset A t) Y r f v =
      fun a => matAct f (FourierSchur.OriginalGroupedFrameFactorization.forwardMask A t)
        (fun y => v (a.1,y)) a.2 := by
  funext a
  exact result_eq_forwardMask A t Y r f v a.1 a.2

/-- Native paid semantic adapter, including raw metadata preparation and all
spectators. The selected transform is an actual open call, not an oracle. -/
theorem run_open_forwardMask_grid {ι : Type*} {m : Bool} {cl : Paint}
    (A : OBase α) (t : Finset α) (X : Layout α)
    (Y : Layout {i : α // i∈t}) (Z : Layout {i : α // i∉t})
    (r : ℕ) (f : ι→ℕ) (v : ∀ i, Grid α r (f i)→ℂ)
    (b : Bank (hatch cl) ι) (τ : ι→ℕ) (hr : 3≤X.n)
    (hB : Small b.B (fun i => (book X r (f i)).n))
    (hc : Rig.RawContract cl b (fun i => Y.n*f i) τ) :
    Able m b (simIn cl) (bundle cl)
      (fun i => givenGrid cl X r (f i) (v i))
      (fun i => (book X r (f i)).tape
        (fun a => matAct (f i)
          (FourierSchur.OriginalGroupedFrameFactorization.forwardMask A t)
          (fun y => v i (a.1,y)) a.2))
      (fun i => (book X r (f i)).n)
      (fun i => (book Z r (f i)).n*τ i) := by
  have H := run_open_grid (m:=m) (v:=v) (ColumnRoute.forSubset A t)
    X Y Z b τ hr hB hc
  refine H.cong (fun _ => rfl) ?_
  intro i
  rw [result_eq_forwardMask_fun]

/-- Closed paid counterpart using the existing shared hills tensor backend. -/
theorem run_closed_forwardMask_grid {ι : Type*} {m : Bool} {cl : Paint}
    (A : OBase α) (t : Finset α) (X : Layout α)
    (Y : Layout {i : α // i∈t}) (Z : Layout {i : α // i∉t})
    (r : ℕ) (f : ι→ℕ) (v : ∀ i, Grid α r (f i)→ℂ)
    (B : ι→ℕ) (hr : 3≤X.n)
    (hB : Small B (fun i => (book X r (f i)).n)) :
    Can m B (simIn cl) (bundle cl)
      (fun i => givenGrid cl X r (f i) (v i))
      (fun i => (book X r (f i)).tape
        (fun a => matAct (f i)
          (FourierSchur.OriginalGroupedFrameFactorization.forwardMask A t)
          (fun y => v i (a.1,y)) a.2))
      (fun i => (book X r (f i)).n*(hills (Y.n*f i)+1)) := by
  have H := run_closed_grid (m:=m) (cl:=cl) (v:=v) (ColumnRoute.forSubset A t)
    X Y Z hr hB
  refine H.cong (fun _ => rfl) ?_
  intro i
  rw [result_eq_forwardMask_fun]

end
end OAI.PowerSaving.RAM.GroupedResidual
