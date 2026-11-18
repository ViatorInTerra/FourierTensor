import vendor.OpenAIUniformFourierBundle

/-!
Actual RAM recursion closure for a variable-order grouped child schedule.

`close_grouped_body` consumes an actual open-code `Able` witness, with its
recursive charge additive and unmultiplied by the local overhead constant.
It produces a closed `Can` program, including polynomial numerical word
bounds. This is a program closure theorem, not an arithmetic recurrence
asserted to execute a tensor transform.

The concrete grouped all-role open body is NOT constructed in this module.
The existing fixed-h32 `PWord` contains expanded individual directions and
does not expose the h100 grouped edge histogram. No h100 histogram, faster
backend axiom, or profile-only premise is substituted for that missing body.
The actual existing hills executor and its program remain unchanged.
-/

namespace FourierSchur.OriginalGroupedRecursionRAM

open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty
open scoped BigOperators
noncomputable section

/-- Fixed finite child kinds, variable child orders and full multiplicities. -/
structure Scheme (σ : Type) [Fintype σ] where
  order : Nat → σ → Nat
  count : Nat → σ → Nat
  decreases : ∀ k t, 0 < count k t → order k t < k

def childCharge {σ : Type} [Fintype σ] (s : Scheme σ) (k : Nat)
    (tau : Nat → Nat) : Nat := ∑ t, s.count k t * tau (s.order k t)

def allowance {σ : Type} [Fintype σ] (s : Scheme σ) (k : Nat) : Nat :=
  2^k + ∑ t, if _h : s.order k t < k then
    s.count k t * allowance s (s.order k t) else 0
termination_by k

theorem allowance_eq {σ : Type} [Fintype σ] (s : Scheme σ) (k : Nat) :
    allowance s k = 2^k + childCharge s k (allowance s) := by
  rw [allowance]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  by_cases h : s.order k t < k
  · simp [h]
  · have hc : s.count k t = 0 := by
      by_contra hh
      exact h (s.decreases k t (Nat.pos_of_ne_zero hh))
    simp [h, hc]

theorem allowance_lower {σ : Type} [Fintype σ] (s : Scheme σ) (k : Nat) :
    2^k ≤ allowance s k := by
  rw [allowance_eq]
  omega

theorem charge_scale {σ : Type} [Fintype σ] (s : Scheme σ) (k c : Nat)
    (tau : Nat → Nat) :
    childCharge s k (fun j => c*tau j) = c*childCharge s k tau := by
  unfold childCharge
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  ring

/-- The actual closure step pays local RAM overhead, the call wrapper, and
every callback with its full multiplicity. The reserve factor is chosen
once for the whole run, rather than multiplied at every recursive level. -/
theorem close_step_bound {σ : Type} [Fintype σ] (s : Scheme σ)
    (C c k : Nat) (hc : 2*C+1 ≤ c) :
    C*(2^k+1)+childCharge s k (fun j => c*allowance s j)+1 ≤
      c*allowance s k := by
  have hp : 1 ≤ (2:Nat)^k := Nat.one_le_pow _ _ (by decide)
  have hs : C*(2^k+1)+1 ≤ c*2^k := by nlinarith
  rw [charge_scale, allowance_eq, Nat.mul_add c]
  omega

/-- The fixed role bits are consumed before the grouped physical macro.
This includes rho=u spare-role calls, whose order is u*floor((k-a)/u). -/
def groupedScheme {σ : Type} [Fintype σ] (u a cutoff : Nat)
    (rho weights : σ → Nat) (ha : 0 < a) (hcut : a ≤ cutoff)
    (hrho : ∀ t, rho t ≤ u) : Scheme σ where
  order k t := rho t * ((k-a)/u)
  count k t := if cutoff ≤ k then weights t * 2^(k-a-rho t*((k-a)/u)) else 0
  decreases k t hc := by
    by_cases hk : cutoff ≤ k
    · have hle : rho t * ((k-a)/u) ≤ k-a := by
        calc
          _ ≤ u*((k-a)/u) := Nat.mul_le_mul_right _ (hrho t)
          _ ≤ _ := by simpa [Nat.mul_comm] using Nat.div_mul_le_self (k-a) u
      omega
    · simp [hk] at hc

theorem grouped_order_bound {σ : Type} [Fintype σ] (u a cutoff : Nat)
    (rho weights : σ → Nat) (ha : 0 < a) (hcut : a ≤ cutoff)
    (hrho : ∀ t, rho t ≤ u) (k : Nat) (t : σ) :
    (groupedScheme u a cutoff rho weights ha hcut hrho).order k t ≤ k-a := by
  change rho t * ((k-a)/u) ≤ k-a
  calc
    _ ≤ u*((k-a)/u) := Nat.mul_le_mul_right _ (hrho t)
    _ ≤ _ := by simpa [Nat.mul_comm] using Nat.div_mul_le_self (k-a) u

theorem grouped_order_strict {σ : Type} [Fintype σ] (u a cutoff : Nat)
    (rho weights : σ → Nat) (ha : 0 < a) (hcut : a ≤ cutoff)
    (hrho : ∀ t, rho t ≤ u) (k : Nat) (hk : cutoff ≤ k) (t : σ) :
    (groupedScheme u a cutoff rho weights ha hcut hrho).order k t < k := by
  have hle := grouped_order_bound u a cutoff rho weights ha hcut hrho k t
  omega

/-- Every spectator copy is charged. The child-volume identity uses the
complete multiplicity, including the full-order spare kind when present. -/
theorem grouped_child_volume {σ : Type} [Fintype σ] (u a cutoff : Nat)
    (rho weights : σ → Nat) (ha : 0 < a) (hcut : a ≤ cutoff)
    (hrho : ∀ t, rho t ≤ u) (k : Nat) (hk : cutoff ≤ k) (t : σ) :
    (groupedScheme u a cutoff rho weights ha hcut hrho).count k t *
      2^((groupedScheme u a cutoff rho weights ha hcut hrho).order k t) =
        weights t * 2^(k-a) := by
  have hle := grouped_order_bound u a cutoff rho weights ha hcut hrho k t
  change rho t * ((k-a)/u) ≤ k-a at hle
  change (if cutoff ≤ k then weights t*2^(k-a-rho t*((k-a)/u)) else 0) *
    2^(rho t*((k-a)/u)) = _
  rw [if_pos hk, Nat.mul_assoc, ← Nat.pow_add]
  rw [Nat.sub_add_cancel hle]

theorem grouped_total_child_volume {σ : Type} [Fintype σ] (u a cutoff : Nat)
    (rho weights : σ → Nat) (ha : 0 < a) (hcut : a ≤ cutoff)
    (hrho : ∀ t, rho t ≤ u) (k : Nat) (hk : cutoff ≤ k) :
    childCharge (groupedScheme u a cutoff rho weights ha hcut hrho) k
      (fun j => 2^j) = 2^(k-a) * ∑ t, weights t := by
  unfold childCharge
  calc
    _ = ∑ t, weights t * 2^(k-a) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact grouped_child_volume u a cutoff rho weights ha hcut hrho k hk t
    _ = _ := by rw [← Finset.sum_mul, Nat.mul_comm]

/-- All lower-order callbacks must implement the exact complete tensor. -/
structure Desc (cl : Paint) where
  k : Nat
  v : Bits k → ℂ
  use : Handler (hatch cl)
  tau : Nat → Nat
  peak : Nat
  works : ∀ j, j < k → ∀ v : Bits j → ℂ,
    (use (givenBits cl j v)).OK ((bits j).tape (ripple j v)) (tau j) peak

def funds (cl : Paint) : Bank (hatch cl) (Desc cl) :=
  ⟨fun i => 2^i.k, Desc.peak, Desc.use⟩

def charge {σ : Type} [Fintype σ] (s : Scheme σ) {cl : Paint} (i : Desc cl) : Nat :=
  childCharge s i.k i.tau

/-- An open body is actual RAM code correct for arbitrary complex inputs,
with exactly the declared additive allowance for every borrowed callback. -/
def OpenBody {σ : Type} [Fintype σ] (s : Scheme σ) (cl : Paint) (m : Bool) : Prop :=
  Able m (funds cl) (simIn cl) (bundle cl)
    (fun i => givenBits cl i.k i.v)
    (fun i => (bits i.k).tape (ripple i.k i.v))
    (fun i => 2^i.k) (charge s)

/-- Close the actual variable-order open body. A single constant scales the
entire allowance; it is not inserted at each recursive charge. -/
theorem close_grouped_body {σ : Type} [Fintype σ] (s : Scheme σ)
    (cl : Paint) (m : Bool) (hbody : OpenBody s cl m)
    {ι : Type} (k : ι → Nat) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i))
      (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => allowance s (k i)) := by
  obtain ⟨body,C,d,hc⟩ := hbody
  let c := 3*C+3
  let base : Prog m (simIn cl) (bundle cl) := .comp (.atom .snd) (.atom .snd)
  let fn := depthRun (base.run ()) body.run
  let P (j : Nat) := (2^j+2)^(d+1)
  have h (depth j : Nat) (hj : j < depth) (v : Bits j → ℂ) :
      (fn depth (givenBits cl j v)).OK ((bits j).tape (ripple j v))
        (c*allowance s j) (max (P j) depth) := by
    induction depth generalizing j with
    | zero => omega
    | succ depth ih =>
      let peak := max (P j) (depth+1)
      have pp (q : Nat) (hq : q < j) (v : Bits q → ℂ) :
          (fn depth (givenBits cl q v)).OK ((bits q).tape (ripple q v))
            (c*allowance s q) peak := by
        have H := ih q (by omega) v
        apply H.mono le_rfl
        have hh : 2^q ≤ 2^j := Nat.pow_le_pow_right (by omega) hq.le
        exact max_le_max (by unfold P; gcongr) (by omega)
      let i : Desc cl := ⟨j,v,fn depth,(fun q => c*allowance s q),peak,pp⟩
      have ht := hc i
      have H := ht.pay (t:=1) (z:=depth+1) (le_trans
        (le_max_right (P j) (depth+1))
        (show peak ≤ (funds cl).cap d i from le_max_right _ _))
      apply H.mono
      · change C*(2^j+1)+charge s i+1 ≤ c*allowance s j
        change C*(2^j+1)+childCharge s j (fun q => c*allowance s q)+1 ≤ _
        exact close_step_bound s C c j (by dsimp [c]; omega)
      · change max _ peak ≤ peak
        apply max_le _ le_rfl
        exact (Small.pow_mono_degree (2^j) (show d ≤ d+1 by omega)).trans
          (le_max_left _ _)
  let B (i : ι) := 2^k i
  let W (i : ι) := allowance s (k i)
  let x (i : ι) := givenBits cl (k i) (v i)
  let X1 (i : ι) : T (p w (simIn cl)) := (k i+1,x i)
  have L : Can m B (p w (simIn cl)) (bundle cl) X1
      (fun i => (bits (k i)).tape (ripple (k i) (v i))) W := by
    refine ⟨.descend base body,c+1,d+1,fun i => ?_⟩
    have H := h (k i+1) (k i) (by omega) (v i)
    have hp : k i+1 ≤ P (k i) := by
      calc
        _ ≤ 2^k i := Nat.lt_two_pow_self
        _ ≤ (2^k i+2)^1 := by simp
        _ ≤ _ := Small.pow_mono_degree _ (by omega)
    have HH := H.pay (t:=1) (z:=k i+1) (le_max_right ..)
    apply HH.mono
    · change c*W i+1 ≤ _
      simp [Nat.add_mul, Nat.mul_add]
      omega
    · exact max_le (le_max_left ..) (hp.trans (le_max_left ..))
  have hsmall : Small B k :=
    (Small.self B).mono (fun i => Nat.lt_two_pow_self.le)
  have HE : Can m B (simIn cl) (p w (simIn cl)) x X1 W := by
    exact ((show Can m B (simIn cl) w x k W from Can.first).plus (Can.wc 1)
      hsmall (Small.const ..)).pair Can.id
  exact HE.then_do L

end
end FourierSchur.OriginalGroupedRecursionRAM
