import work_in_progress.OriginalLocalizedBankSharing

/-! The actual native center image has 30 independent generated rows.
The 33 arbitrary original center inputs are a different bank and are
not compressed or discarded by this construction. -/
namespace FourierSchur.OriginalNativeCenterSharing
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.Cluster Matrix Finset
open scoped BigOperators
noncomputable section

abbrev Free := {i : H // i ∈ freeSet}

def freeRows : Matrix Free Trip ℚ := fun i t => if i.val ∈ t.val then 1 else 0

def expandCenter (q : ℚ) : Matrix Center Free ℚ
  | .inl (), _ => q
  | .inr i, k => if i=k.val then 1 else 0

theorem free_card : Fintype.card Free=30 := by
  rw [Fintype.card_coe,freeSet,Finset.card_sdiff_of_subset (subset_univ _)]
  decide

theorem free_column_sum (t : Trip) : (∑ i : Free, freeRows i t)=3 := by
  have he : freeSet.filter (fun i => i∈t.val)=t.val := by
    ext i
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun h => trip_sub t h)
  calc
    (∑ i : Free, freeRows i t)=∑ i∈freeSet, if i∈t.val then (1:ℚ) else 0 :=
      by simpa only [freeRows] using
        (Finset.sum_coe_sort freeSet (fun i => if i∈t.val then (1:ℚ) else 0))
    _ = ((freeSet.filter (fun i => i∈t.val)).card:ℚ) := by
      simp
      congr 1
    _ = 3 := by rw [he,trip_card]; norm_num

theorem expand_unit (q : ℚ) (t : Trip) :
    (expandCenter q * freeRows) (.inl ()) t=3*q := by
  simp only [Matrix.mul_apply,expandCenter,← mul_sum]
  rw [free_column_sum]
  ring

theorem expand_coordinate (q : ℚ) (i : H) (t : Trip) :
    (expandCenter q * freeRows) (.inr i) t=if i∈t.val then 1 else 0 := by
  rw [Matrix.mul_apply]
  by_cases hi : i∈freeSet
  · rw [Finset.sum_eq_single (⟨i,hi⟩ : Free)]
    · simp [expandCenter,freeRows]
    · intro k _ hk
      have hn : i≠k.val := fun h => hk (Subtype.ext h.symm)
      simp [expandCenter,hn]
    · simp
  · have ht : i∉t.val := fun h => hi (trip_sub t h)
    have hz (k : Free) : i≠k.val := fun h => hi (h ▸ k.property)
    simp [expandCenter,hz,ht]

/-- The generated G-image factors through exactly 30 fixed rational rows.
This is an identity for the native matrices, with no numerical-rank or
small-residual hypothesis on the complex input. -/
theorem glocal_factor : glocal=expandCenter (1/3)*freeRows := by
  ext c t
  cases c with
  | inl c =>
    cases c
    rw [expand_unit]
    norm_num [glocal]
  | inr i => exact (expand_coordinate (1/3) i t).symm

/-- The inverse-transpose invocation has the same 30-row compression,
with the opposite unit-row reconstruction. -/
theorem rmat_transpose_factor :
    rmatᵀ=expandCenter (-1/3)*((1/2:ℚ) • freeRows) := by
  rw [Matrix.mul_smul]
  ext c t
  cases c with
  | inl c =>
    cases c
    norm_num [Matrix.smul_apply,expand_unit,rlocal,rmat]
  | inr i =>
    simp only [Matrix.smul_apply,smul_eq_mul,expand_coordinate,
      Matrix.transpose_apply,rmat,Matrix.of_apply,rlocal]
    ring

/-- Forward output reconstruction is one fixed rational point map.
Its application is charged by the localized native sharing compiler. -/
def forwardConsumer : Matrix Trip Free ℚ := rmat*expandCenter (1/3)

def sourceRows : Matrix Free Box ℚ
  | k, .inl (.inl t) => freeRows k t
  | _, _ => 0

def targetRows : Matrix Box Free ℚ
  | .inl (.inr t), k => forwardConsumer t k
  | _, _ => 0

def centerWord {α : Type*} (S T : Finset α) :
    OriginalGroupedFrameWords.Word α (Box ⊕ Free) :=
  OriginalLocalizedBankSharing.sharedRatioWord sourceRows targetRows S T

theorem forward_factor : rmat*glocal=forwardConsumer*freeRows := by
  rw [glocal_factor,forwardConsumer,Matrix.mul_assoc]

theorem backward_factor :
    glocalᵀ*rmatᵀ=(glocalᵀ*expandCenter (-1/3))*((1/2:ℚ) • freeRows) := by
  rw [rmat_transpose_factor,Matrix.mul_assoc]

section CommonTransform
variable {ν : Type*} [Fintype ν]

/-- This identity moves the SAME paid transform through a fixed rational
row catalogue. It does not identify kernels in different frames. -/
theorem transform_catalogue (T : Matrix ν ν ℂ) (E : Matrix Center Free ℚ)
    (z : Free → ν → ℂ) (c : Center) (a : ν) :
    (T *ᵥ (fun b => ∑ k, (E c k:ℂ)*z k b)) a=
      ∑ k, (E c k:ℂ)*(T *ᵥ z k) a := by
  simp only [Matrix.mulVec, dotProduct, mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Exact full generated-center transfer, on arbitrary complex row banks.
The right side executes only the 30 common-transform rows. -/
theorem forward_correction (T : Matrix ν ν ℂ) (x : Trip → ν → ℂ)
    (t : Trip) (a : ν) :
    (∑ c : Center, (rmat t c:ℂ)*
      (T *ᵥ (fun b => ∑ j, (glocal c j:ℂ)*x j b)) a)=
    ∑ k : Free, (forwardConsumer t k:ℂ)*
      (T *ᵥ (fun b => ∑ j, (freeRows k j:ℂ)*x j b)) a := by
  have hinput (c : Center) :
      (fun b => ∑ j, (glocal c j:ℂ)*x j b)=
      (fun b => ∑ k, (expandCenter (1/3) c k:ℂ)*
        (∑ j, (freeRows k j:ℂ)*x j b)) := by
    funext b
    rw [glocal_factor]
    simp only [Matrix.mul_apply,Rat.cast_sum,Rat.cast_mul,
      Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hinput,transform_catalogue]
  simp only [forwardConsumer,Matrix.mul_apply,Rat.cast_sum,Rat.cast_mul,
    Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro c _
  ring
end CommonTransform

section LocalWord
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Original center and side banks, and original X banks, remain intact
in this generated-correction word. They are not fresh scratch. -/
theorem centerWord_original_aux (A : (Box ⊕ Free) → OBase α)
    (S T : Finset α) (f : ℕ) (x : Data α (Box ⊕ Free) f) (c : Aux) :
    OriginalGroupedFrameWords.walk A f (centerWord S T) x (.inl (.inr c))=
      x (.inl (.inr c)) := by
  apply OriginalLocalizedBankSharing.sharedRatioWord_preserves
  intro k
  rfl

/-- On the target bank this is the full native R / common transform / G
correction, including all original independent X rows. -/
theorem centerWord_target (A : (Box ⊕ Free) → OBase α) (A0 : OBase α)
    (hA : ∀ k, A (.inr k)=A0) (S T : Finset α) (f : ℕ)
    (x : Data α (Box ⊕ Free) f) (t : Trip) (a : Sky α f) :
    OriginalGroupedFrameWords.walk A f (centerWord S T) x (.inl (byy t)) a=
      x (.inl (byy t)) a+
      ∑ c : Center, (rmat t c:ℂ)*matAct f (frame A0 T * unframe A0 S)
        (fun b => ∑ j, (glocal c j:ℂ)*x (.inl (bx j)) b) a := by
  rw [centerWord,OriginalLocalizedBankSharing.sharedRatioWord_correct]
  simp only [targetRows,sourceRows,Fintype.sum_sum_type,hA,
    Rat.cast_zero,zero_mul,Finset.sum_const_zero,add_zero]
  congr 1
  simpa only [matAct,Fintype.sum_sum_type] using
    (forward_correction (digitProd (fun _ : Fin f => frame A0 T * unframe A0 S))
      (fun j b => x (.inl (bx j)) b) t a).symm

/-- Physical width of the GENERATED center roots only, including all
spectators. This sparsity does not include other recursive requests in
the complete shared network. -/
theorem generated_center_roots_sparse (width : ℕ) :
    4*(Fintype.card Free*width)≤Fintype.card Box*width := by
  have h : 4*Fintype.card Free≤Fintype.card Box := by
    rw [free_card]
    simp only [Fintype.card_sum,Fintype.card_prod,num_trip]
    norm_num
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right width h
end LocalWord

/-- Complete spectator-inclusive child bill for this generated image.
The 33 original arbitrary center banks retain their separate terminal bill. -/
theorem generated_center_charge {α : Type*} [Fintype α] [DecidableEq α]
    (X : Layout α) (r f : ℕ) (tau : ℕ → ℕ) (S : Finset α)
    (B : Matrix Free Box ℚ) (D : Matrix Box Free ℚ) :
    OriginalGroupedWordRAM.wordCharge X r f tau
      (OriginalLocalizedBankSharing.sharedWord B D S)=
      30 * (if S.card=0 then 0 else
        (2^r*(2^f)^(X.n-S.card))*tau (S.card*f)) := by
  rw [OriginalLocalizedBankSharing.sharedWord_charge,free_card]

section NativeRAM
open OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
universe U
variable {α : Type*} [Fintype α] [DecidableEq α] {ι : Type U}
  {m : Bool} {cl : Paint} {f : ι → ℕ} {s : Ty} {x : ι → T s}
  {X : Layout α} {R : Layout (Box ⊕ Free)} {r : ℕ}
  {v : ∀ i, Grain α (Box ⊕ Free) r (f i)}

/-- Concrete native code for the actual G/R generated image. Coefficient
preparation, scratch assembly and clearing, arithmetic and all routing
are paid by the native point and frame loops. This is an open local
routine; the surrounding network and terminal original-center kernels
are not removed by this theorem. -/
theorem centerWord_native (b : Bank (hatch cl) ι)
    (h : Rig m b.B f s x cl X R r v) (hr : 3≤X.n)
    (A : (Box ⊕ Free) → OBase α) (tau : ι → ℕ → ℕ)
    (HC : ∀ n : ℕ, 0<n → n≤X.n → GroupedResidual.Rig.RawContract cl b
      (fun i => n*f i) (fun i => tau i (n*f i))) (S T : Finset α) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape
        (OriginalGroupedWordRAM.coastline A r (f i) (centerWord S T) (v i)))
      (fun i => (fleet X R r (f i)).n)
      (fun i => 30 * (if ((S\T) ∪ (T\S)).card=0 then 0 else
        (2^r*(2^f i)^(X.n-((S\T) ∪ (T\S)).card))*tau i (((S\T) ∪ (T\S)).card*f i))) := by
  simpa only [centerWord,free_card] using
    OriginalLocalizedBankSharing.sharedRatioWord_native b h hr A tau HC sourceRows targetRows S T
end NativeRAM

end
end FourierSchur.OriginalNativeCenterSharing
