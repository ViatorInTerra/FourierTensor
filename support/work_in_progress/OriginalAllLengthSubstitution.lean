import work_in_progress.OriginalArbitraryLengthSubstitution

/-! Actual all-length Fourier compiler composition, including the direct
fallback when `Ports` is false. The tensor executor remains an explicit
uniform RAM certificate; the receipt root is an input, its order is computed
by the original paid program, and all produced integer caps remain checked
by `Can`. No faster tensor profile or global density is instantiated. -/

namespace FourierSchur.OriginalAllLengthSubstitution
open OAI.PowerSaving OAI.PowerSaving.Selection OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty OAI.PowerSaving.RAM.Bench
open Spectral
open OriginalCompilerRootBridge OriginalSectorSubstitution
noncomputable section
universe U

def fairwind (profile : ℕ → ℕ) (d n : ℕ) : ℕ :=
  OriginalArbitraryLengthSubstitution.Bench.surf profile d n (stackN n) +
    (if Ports n then 0 else (n+2)^d)

theorem fairwind_deg {profile : ℕ → ℕ} {c d : ℕ} (n : ℕ) (h : c ≤ d) :
    fairwind profile c n ≤ fairwind profile d n := by
  unfold fairwind
  refine Nat.add_le_add
    (OriginalArbitraryLengthSubstitution.Bench.surf_deg (profile:=profile) _ _ h) ?_
  split
  · exact le_rfl
  · exact Small.pow_mono_degree n h

theorem fairwind_left (profile : ℕ → ℕ) (n d : ℕ) :
    n+(stackN n+2)^d ≤ fairwind profile d n := by
  unfold fairwind OriginalArbitraryLengthSubstitution.Bench.surf
  omega

theorem fairwind_n (profile : ℕ → ℕ) (n d : ℕ) : n ≤ fairwind profile d n :=
  (Nat.le_add_right _ _).trans (fairwind_left profile n d)

variable {m : Bool} {ι : Type U} {b : OAI.PowerSaving.RAM.Bench m ι}
  {n N : ι → ℕ} {profile : ℕ → ℕ} {cl : Paint} {x : ι → Line}

/-- The actual runtime branch test chooses the synchronized chirp compiler
or the original polynomial direct Fourier program. -/
theorem course_supplied
    (hExec : SuppliedTensorExecutor sc parentRoot cl m profile)
    (hScalar : SuppliedTensorExecutor sc parentRoot .scalar m profile)
    (hmono : Monotone profile) (h : b.Neaps (fun i => stackN (n i)) n)
    (hz : b.Moves (fun _ => 0) sc (fun i => root (receipt (n i))))
    (r : Bool)
    (hx : b.Moves (fun _ => 0) (a (c cl)) (fun i => Tape.tab (n i) (x i))) :
    ∃ d : ℕ, b.Moves (fun i => fairwind profile d (n i)) (a (c cl))
      (fun i => Tape.tab (n i) (freq (n i) (pr r (n i)) (x i))) := by
  let flag (i : ι) := if Ports (n i) then 0 else 1
  let P0 (i : ι) := flag i=0
  let P1 (i : ι) := flag i≠0
  have F0 := Instant.along b (Subtype.val (p:=P0))
  have F1 := Instant.along b (Subtype.val (p:=P1))
  have hp0 : ∀ i : Subtype P0, Ports (n i.val) := fun i => by
    by_contra hn
    have hi : flag i.val=0 := i.property
    simp [flag,hn] at hi
  have hp1 : ∀ i : Subtype P1, ¬ Ports (n i.val) :=
    fun i hi => i.property (by simp [flag,hi])
  obtain ⟨d0,h0⟩ := h.portG.dry
  obtain ⟨dB,hB⟩ := OriginalArbitraryLengthSubstitution.Bench.Neaps.swift_supplied
    hExec hScalar hmono (h.transfer F0) hp0 ((hz.transfer F0).dunes _)
    r (hx.transfer F0)
  let H := h.transfer F1
  have hroot := signP r H.pos
    (((hz.transfer F1).dunes (fun i => n i.val)).congr
      (y:=fun i : Subtype P1 => root (n i.val))
      (fun i => by rw [receipt,if_neg (hp1 i)]))
  obtain ⟨dD,hD⟩ := Dry.dire H.num ((hx.transfer F1).dunes _) hroot
  let d := d0+dB+dD
  refine ⟨d,Can.testz (W:=fun i => fairwind profile d (n i)) (n:=flag) ?_ ?_ ?_⟩
  · exact Can.mono h0 (fun i =>
      (Nat.le_add_left _ _).trans ((fairwind_left profile (n i) d0).trans
        (fairwind_deg (n i) (by unfold d; omega))))
  · exact Can.mono hB (fun i =>
      (OriginalArbitraryLengthSubstitution.Bench.surf_deg (profile:=profile)
        (stackN (n i.val)) (n i.val) (show dB ≤ d by unfold d; omega)).trans
        (Nat.le_add_right _ _))
  · exact Can.mono hD (fun i => by
      have hpow : (n i.val+2)^dD ≤ (n i.val+2)^d :=
        Small.pow_mono_degree (n i.val) (show dD ≤ d by unfold d; omega)
      change (n i.val+2)^dD ≤ fairwind profile d (n i.val)
      unfold fairwind
      rw [if_neg (hp1 i)]
      exact hpow.trans (Nat.le_add_left _ _))

/-- Runtime stack-size preparation is charged before either Fourier branch. -/
theorem land_supplied
    (hExec : SuppliedTensorExecutor sc parentRoot cl m profile)
    (hScalar : SuppliedTensorExecutor sc parentRoot .scalar m profile)
    (hmono : Monotone profile) (h : b.Nick N) (g : ∀ i, 0<N i)
    (hz : b.Moves (fun _ => 0) sc (fun i => root (receipt (N i))))
    (r : Bool)
    (hx : b.Moves (fun _ => 0) (a (c cl)) (fun i => Tape.tab (N i) (x i))) :
    ∃ d : ℕ, b.Moves (fun i => fairwind profile d (N i)) (a (c cl))
      (fun i => Tape.tab (N i) (freq (N i) (pr r (N i)) (x i))) := by
  obtain ⟨hu,hk⟩ := h.stackH g
  have F := Instant.extend b (fun i => stackN (N i)) (t:=w)
  obtain ⟨d,hd⟩ := course_supplied hExec hScalar hmono hk
    (hz.transfer F) r (hx.transfer F)
  exact ⟨d,caseM (t:=w) (x:=fun (i : ι) => stackN (N i))
    (hu.weaken (Dom.of_le (fun i => fairwind_n profile (N i) d))) hd⟩

/-- The order program is the original integer-only paid computation. -/
theorem landOrder {profile : ℕ → ℕ} (h : b.Nick N) (g : ∀ i, 0<N i) :
    ∃ d : ℕ, b.Moves (fun i => fairwind profile d (N i)) w
      (fun i => receipt (N i)) := by
  obtain ⟨d,hd⟩ := h.planOrder g
  exact ⟨d,hd.weaken (Dom.of_le (fun i => fairwind_left profile (N i) d))⟩

/-- One finite program handles every positive length and arbitrary complex
input. The profile-dependent work and the polynomial integer cap are stated
directly, without applying the original hardcoded density estimate. -/
theorem executeOne_supplied
    (hExec : SuppliedTensorExecutor sc parentRoot .left false profile)
    (hScalar : SuppliedTensorExecutor sc parentRoot .scalar false profile)
    (hmono : Monotone profile) :
    ∃ (program : Prog false dftInKind dftOutKind) (d C p : ℕ),
      ∀ (n : ℕ), 0<n → ∀ x : Vec n,
      (run program (n,root (receipt n),(⟨n,x⟩ : Tape ℂ))).OK
        (⟨n,dft n x⟩ : Tape ℂ)
        (C*(fairwind profile d n+1)) ((n+2)^p) := by
  let K := towerOne
  have ht : K.Moves (fun _ => 0) dftInKind K.env := envNow K
  let n (i : Sizes × Line) := entry i.1
  have hk : K.Nick n := ⟨ht.fst,Small.self _⟩
  obtain ⟨d,hd⟩ := land_supplied hExec hScalar hmono hk
    (fun i => i.1.property) ht.snd.fst false (x:=Prod.snd) ht.snd.snd
  obtain ⟨program,C,p,hp⟩ := Can.unfold_bound hd
  refine ⟨program,d,C,p,fun n hn x => ?_⟩
  specialize hp ((⟨n,hn⟩ : Sizes),extendLine x)
  change (run program (n,root (receipt n),
    (⟨n,front n (extendLine x)⟩ : Tape ℂ))).OK
    (⟨n,front n (freq n (pr false n) (extendLine x))⟩ : Tape ℂ) _ _ at hp
  rw [← dft_front n,front_exact] at hp
  exact hp

end
end FourierSchur.OriginalAllLengthSubstitution
