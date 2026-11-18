import vendor.OpenAIUniformFourierBundle
import work_in_progress.OriginalGroupedResidualCertificate

/-! Actual native 32-coordinate masks underlying the grouped edge ranks.
These facts identify retained full frame changes with their tensor orders.
They do not count neighbor roles or compile the retained requests. -/

namespace FourierSchur.OriginalGroupedMaskCards
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.Cluster Finset
open OriginalGroupedResidualCertificate
noncomputable section
set_option maxHeartbeats 2000000

theorem card_rect_true (j : J) (s : Finset H) :
    (rect j true s).card=32^j.val*s.card := by
  rw [rect,Fintype.card_piFinset,Fin.prod_univ_three]
  fin_cases j
  · change s.card*1*1=32^0*s.card
    ring
  · change 32*s.card*1=32^1*s.card
    ring
  · change 32*32*s.card=32^2*s.card
    ring

theorem card_rect_false (j : J) (s : Finset H) :
    (rect j false s).card=s.card := by
  rw [rect,Fintype.card_piFinset]
  fin_cases j <;> simp [sets,Fin.prod_univ_succ]

theorem rect_false_subset_true (j : J) (s : Finset H) :
    rect j false s ⊆ rect j true s := by
  intro x hx
  rw [mem_rect] at hx ⊢
  exact ⟨hx.1,by simp,hx.2.2⟩

theorem card_big (j : J) : (big j).card=32^(j.val+1) := by
  simp [big,card_rect_true,pow_succ]

theorem card_belt (j : J) : (belt j).card=(32^j.val-1)*32 := by
  rw [belt,card_sdiff_of_subset (rect_le_big j false univ),card_big,card_rect_false]
  fin_cases j <;> norm_num

theorem card_xstart (j : J) (slot : H) : (xstart j slot).card=32^j.val := by
  simp [xstart,card_rect_true]

theorem card_ystart (j : J) (slot : H) : (ystart j slot).card=32^j.val-1 := by
  rw [ystart,xstart,card_sdiff_of_subset (rect_false_subset_true j {slot}),
    card_rect_true,card_rect_false,card_singleton,mul_one]

theorem card_xstep (j : J) (slot : H) :
    (xstep j slot).card=32^(j.val+1)-31 := by
  rw [xstep,card_sdiff_of_subset (rect_le_big j false _),card_big,card_rect_false]
  have hs : (univ \ {slot}:Finset H).card=31 := by
    rw [card_sdiff_of_subset (subset_univ ({slot}:Finset H))]
    norm_num
  rw [hs]

theorem card_ystep (j : J) (slot : H) :
    (ystep j slot).card=32^(j.val+1)-1 := by
  rw [ystep,card_sdiff_of_subset (rect_le_big j false _),card_big,
    card_rect_false,card_singleton]

theorem card_blocks : Fintype.card Blocks=32768 := by
  norm_num [Fintype.card_fun]

theorem xstart_subset_xstep (j : J) (slot : H) :
    xstart j slot ⊆ xstep j slot := by
  intro x hx
  rw [in_xstart] at hx
  rw [in_xstep]
  exact ⟨hx.1,Or.inr hx.2⟩

theorem ystart_subset_belt (j : J) (slot : H) :
    ystart j slot ⊆ belt j := by
  intro x hx
  rw [in_ystart] at hx
  exact (in_belt j x).mpr ⟨hx.1,hx.2.1⟩

theorem ystart_one_subset_xstep_zero (j : J) :
    ystart j 1 ⊆ xstep j 0 := by
  intro x hx
  rw [in_ystart] at hx
  exact (in_xstep j 0 x).mpr ⟨hx.1,Or.inl hx.2.1⟩

theorem xstep_zero_subset_ystep_one (j : J) :
    xstep j 0 ⊆ ystep j 1 := by
  intro x hx
  rw [in_xstep] at hx
  apply (in_ystep j 1 x).mpr
  refine ⟨hx.1,?_⟩
  rcases hx.2 with hp|hs
  · exact Or.inl hp
  · exact Or.inr (hs ▸ piv)

def stageRanks (j : J) : Fin 10 → ℕ :=
  ![((xstep j 0) \ xstart j 0).card,
    ((big j) \ xstep j 0).card,
    (belt j).card,
    ((big j) \ belt j).card,
    (univ \ big j).card,
    (ystart j 1).card,
    ((xstep j 0) \ ystart j 1).card,
    ((ystep j 1) \ xstep j 0).card,
    ((big j) \ ystep j 1).card,
    (univ \ big j).card]

theorem stageRanks_eq (j : J) (i : Fin 10) :
    stageRanks j i=edgeRank 32 j.val i := by
  have hxs : xstep j 0 ⊆ big j := by
    intro x hx
    exact (in_big j x).mpr ((in_xstep j 0 x).mp hx).1
  have hys : ystep j 1 ⊆ big j := by
    intro x hx
    exact (in_big j x).mpr ((in_ystep j 1 x).mp hx).1
  have hr1 := card_sdiff_of_subset (xstart_subset_xstep j 0)
  have hr2 := card_sdiff_of_subset hxs
  have hr4 := belt_drop j
  have hr5 := card_sdiff_of_subset (subset_univ (big j))
  have hr7 := card_sdiff_of_subset (ystart_one_subset_xstep_zero j)
  have hr8 := card_sdiff_of_subset (xstep_zero_subset_ystep_one j)
  have hr9 := card_sdiff_of_subset hys
  fin_cases i <;> simp only [stageRanks,
    hr1,hr2,hr4,hr5,hr7,hr8,hr9,card_xstep,card_xstart,card_big,card_belt,
    card_ystart,card_ystep,card_univ,card_blocks] <;>
    fin_cases j <;> norm_num [edgeRank]

end
end FourierSchur.OriginalGroupedMaskCards
