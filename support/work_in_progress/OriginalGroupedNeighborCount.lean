import vendor.OpenAIUniformFourierBundle

/-! The actual native graph is on triples from 30 free coordinates.
The intersection partition proves its degree, rather than importing the
publication's different 100-coordinate geometry. -/

namespace FourierSchur.OriginalGroupedNeighborCount
open OAI.PowerSaving OAI.PowerSaving.Cluster Finset
noncomputable section
set_option maxHeartbeats 2000000

theorem card_freeSet : freeSet.card=30 := by
  rw [freeSet,card_sdiff_of_subset (subset_univ _)]
  simp

theorem card_outside (x : Trip) : (freeSet \ x.val).card=27 := by
  rw [card_sdiff_of_subset (trip_sub x),card_freeSet,trip_card]

abbrev MeetClass (x : Trip) (k : ℕ) := {y : Trip // meet x y=k}
abbrev Pieces (x : Trip) (k : ℕ) :=
  (↑(x.val.powersetCard k)) × (↑((freeSet \ x.val).powersetCard (3-k)))

def splitMeet (x : Trip) (k : ℕ) (y : MeetClass x k) : Pieces x k := by
  refine (⟨x.val ∩ y.val.val,?_⟩,⟨y.val.val \ x.val,?_⟩)
  · apply mem_powersetCard.mpr
    exact ⟨inter_subset_left,y.property⟩
  · apply mem_powersetCard.mpr
    constructor
    · intro a ha
      obtain ⟨hy,hx⟩ := mem_sdiff.mp ha
      exact mem_sdiff.mpr ⟨trip_sub y.val hy,hx⟩
    · have h := card_sdiff_add_card_inter y.val.val x.val
      have hi : (y.val.val ∩ x.val).card=k := by
        rw [inter_comm]
        exact y.property
      rw [trip_card,hi] at h
      omega

def joinMeet (x : Trip) (k : ℕ) (hk : k≤3) (p : Pieces x k) : MeetClass x k := by
  have ha := mem_powersetCard.mp p.1.property
  have hb := mem_powersetCard.mp p.2.property
  have hd : Disjoint p.1.val p.2.val := by
    apply disjoint_left.mpr
    intro a ha' hb'
    exact (mem_sdiff.mp (hb.1 hb')).2 (ha.1 ha')
  have hi : x.val ∩ (p.1.val ∪ p.2.val)=p.1.val := by
    ext a
    simp only [mem_inter,mem_union]
    constructor
    · rintro ⟨hx,ha'|hb'⟩
      · exact ha'
      · exact False.elim ((mem_sdiff.mp (hb.1 hb')).2 hx)
    · intro ha'
      exact ⟨ha.1 ha',Or.inl ha'⟩
  refine ⟨⟨p.1.val ∪ p.2.val,mem_powersetCard.mpr ⟨?_,?_⟩⟩,?_⟩
  · intro a hg
    obtain h|h := mem_union.mp hg
    · exact trip_sub x (ha.1 h)
    · exact (mem_sdiff.mp (hb.1 h)).1
  · rw [card_union_of_disjoint hd,ha.2,hb.2]
    omega
  · change (x.val ∩ (p.1.val ∪ p.2.val)).card=k
    rw [hi,ha.2]

def meetPiecesEquiv (x : Trip) (k : ℕ) (hk : k≤3) : MeetClass x k ≃ Pieces x k where
  toFun := splitMeet x k
  invFun := joinMeet x k hk
  left_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    change (x.val ∩ y.val.val) ∪ (y.val.val \ x.val)=y.val.val
    rw [inter_comm,union_comm,sdiff_union_inter]
  right_inv p := by
    apply Prod.ext <;> apply Subtype.ext
    · change x.val ∩ (p.1.val ∪ p.2.val)=p.1.val
      have ha := (mem_powersetCard.mp p.1.property).1
      have hb := (mem_powersetCard.mp p.2.property).1
      ext a
      simp only [mem_inter,mem_union]
      constructor
      · rintro ⟨hx,ha'|hb'⟩
        · exact ha'
        · exact False.elim ((mem_sdiff.mp (hb hb')).2 hx)
      · intro ha'
        exact ⟨ha ha',Or.inl ha'⟩
    · change (p.1.val ∪ p.2.val) \ x.val=p.2.val
      have ha := (mem_powersetCard.mp p.1.property).1
      have hb := (mem_powersetCard.mp p.2.property).1
      ext a
      simp only [mem_sdiff,mem_union]
      constructor
      · rintro ⟨ha'|hb',hx⟩
        · exact False.elim (hx (ha ha'))
        · exact hb'
      · intro hb'
        exact ⟨Or.inr hb',(mem_sdiff.mp (hb hb')).2⟩

theorem meet_class_card (x : Trip) (k : ℕ) (hk : k≤3) :
    Fintype.card (MeetClass x k)=Nat.choose 3 k*Nat.choose 27 (3-k) := by
  rw [Fintype.card_congr (meetPiecesEquiv x k hk)]
  simp only [Pieces,Fintype.card_prod,Fintype.card_coe,card_powersetCard,
    trip_card,card_outside]

def neighborEquiv (x : Trip) :
    {y : Trip // neighbor x y} ≃ MeetClass x 0 ⊕ MeetClass x 2 where
  toFun y := if h : meet x y.val=0 then .inl ⟨y.val,h⟩
    else .inr ⟨y.val,y.property.resolve_left h⟩
  invFun y := match y with
    | .inl y => ⟨y.val,Or.inl y.property⟩
    | .inr y => ⟨y.val,Or.inr y.property⟩
  left_inv y := by
    by_cases h : meet x y.val=0 <;> simp [h]
  right_inv y := by
    cases y with
    | inl y => simp [y.property]
    | inr y =>
      have h : meet x y.val≠0 := by rw [y.property]; decide
      simp [h]

theorem neighbor_degree (x : Trip) : Fintype.card {y : Trip // neighbor x y}=3006 := by
  rw [Fintype.card_congr (neighborEquiv x),Fintype.card_sum,
    meet_class_card x 0 (by omega),meet_class_card x 2 (by omega)]
  norm_num [Nat.choose_eq_descFactorial_div_factorial]

abbrev NeighborSide := {p : Side // neighbor p.1 p.2}

def sideEquiv : NeighborSide ≃ (Σ x : Trip, {y : Trip // neighbor x y}) where
  toFun p := ⟨p.val.1,⟨p.val.2,p.property⟩⟩
  invFun p := ⟨(p.1,p.2.val),p.2.property⟩
  left_inv p := rfl
  right_inv p := rfl

theorem neighbor_side_card : Fintype.card NeighborSide=4060*3006 := by
  rw [Fintype.card_congr sideEquiv,Fintype.card_sigma]
  simp only [neighbor_degree,Finset.sum_const,Finset.card_univ,num_trip,smul_eq_mul]


end
end FourierSchur.OriginalGroupedNeighborCount
