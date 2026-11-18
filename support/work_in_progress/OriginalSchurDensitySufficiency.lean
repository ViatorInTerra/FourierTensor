import work_in_progress.OriginalAllLengthSubstitution

/-! A sufficient complete tensor density for the actual all-length compiler.
The hypothesis bounds the work of a supplied uniform RAM executor, including
its own routing and coefficient preparation. It does not assert that such a
Schur executor has been constructed. The compiler's additional preparation,
shorter axes, synchronized layers, fallback and integer caps are retained. -/

namespace FourierSchur.OriginalSchurDensitySufficiency
open OAI.PowerSaving OAI.PowerSaving.Selection OAI.PowerSaving.Slant
open OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty OAI.PowerSaving.RAM.Bench
open OAI.PowerSaving.Skies Filter Asymptotics Real
open OriginalCompilerRootBridge OriginalSectorSubstitution
noncomputable section

/-- Multiplicative form of the complete density bound
`profile(k)+1 ≤ c*sqrt(k+1)/log(k+2)^2`. The `+1` pays routing. -/
def SqrtLogProfile (profile : ℕ → ℕ) (c : ℝ) : Prop :=
  0 ≤ c ∧ ∀ k : ℕ,
    ((profile k : ℝ)+1)*(Real.log ((k : ℝ)+2))^2 ≤ c*Real.sqrt ((k : ℝ)+1)

def flight (n : ℕ) : ℝ := (n : ℝ)*Real.sqrt (Tm n)

/-- The original stack count is also a lower bound for the natural logarithm.
This is the lower bound needed to cancel the synchronized layer logarithms. -/
theorem stack_log_lower (n N : ℕ) (hn : 0<n) (h : n≤N) :
    Tm n ≤ (stackN N : ℝ) := by
  have hp : n ≤ 2^(stackN N) := by
    have hh := stack_above N
    omega
  have H := Real.log_le_log (show 0<(n : ℝ) by exact_mod_cast hn)
    (show (n : ℝ) ≤ (2 : ℝ)^(stackN N) by exact_mod_cast hp)
  rw [Real.log_pow] at H
  have h2 := Real.log_le_sub_one_of_pos (show 0<(2 : ℝ) by norm_num)
  have hs : 0 ≤ (stackN N : ℝ) := by positivity
  change Real.log (n : ℝ) ≤ _
  nlinarith

theorem log_stack_lower (n N : ℕ) (hn : 0<n) (h : n≤N)
    (ht : 1≤Tm n) :
    Qm n ≤ Real.log ((stackN N : ℝ)+2) := by
  exact Real.log_le_log (by linarith : 0<Tm n)
    (by have hh := stack_log_lower n N hn h; linarith)

/-- Monotonicity covers every shorter axis using the original stack bound;
no live tensor is enlarged. The two logarithms exactly pay `score_lim`. -/
theorem weighted_profile_lim {profile : ℕ → ℕ} {c : ℝ}
    (hd : SqrtLogProfile profile c) (hmono : Monotone profile)
    (n N : ℕ) (hn : 0<n) (h : n≤N) (hk : N≤2*n)
    (ht : 1≤Tm n) (hu : 1≤Qm n) :
    (Qm n)^2*((profile (barge N).l : ℝ)+1) ≤ 4*c*Real.sqrt (Tm n) := by
  have hl : (barge N).l ≤ stackN N := (barge_spec N (by omega)).count
  have hprof : (profile (barge N).l : ℝ)+1 ≤ (profile (stackN N) : ℝ)+1 := by
    exact_mod_cast Nat.add_le_add_right (hmono hl) 1
  have hlog := log_stack_lower n N hn h ht
  have hQ : 0≤Qm n := by linarith
  have hlog0 : 0≤Real.log ((stackN N : ℝ)+2) := by linarith
  have hsq : (Qm n)^2 ≤ (Real.log ((stackN N : ℝ)+2))^2 := by
    nlinarith
  have H : (Qm n)^2*((profile (barge N).l : ℝ)+1) ≤
      c*Real.sqrt ((stackN N : ℝ)+1) := by
    calc
      _ ≤ (Real.log ((stackN N : ℝ)+2))^2*
          ((profile (stackN N) : ℝ)+1) :=
        mul_le_mul hsq hprof (by positivity) (sq_nonneg _)
      _ = ((profile (stackN N) : ℝ)+1)*
          (Real.log ((stackN N : ℝ)+2))^2 := by ring
      _ ≤ _ := hd.2 (stackN N)
  have hs := stack_lim n N hn h hk ht
  have hsqrt : Real.sqrt ((stackN N : ℝ)+1) ≤ 4*Real.sqrt (Tm n) := by
    calc
      _ ≤ Real.sqrt (16*Tm n) := Real.sqrt_le_sqrt (by linarith)
      _ = 4*Real.sqrt (Tm n) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ)≤16)]
        norm_num
  calc
    _ ≤ c*Real.sqrt ((stackN N : ℝ)+1) := H
    _ ≤ c*(4*Real.sqrt (Tm n)) := mul_le_mul_of_nonneg_left hsqrt hd.1
    _ = _ := by ring

theorem leg_lim {profile : ℕ → ℕ} {c : ℝ}
    (hd : SqrtLogProfile profile c) (hmono : Monotone profile)
    (n N : ℕ) (hn : 0<n) (h : n≤N) (hk : N≤2*n)
    (ht : 1≤Tm n) (hu : 1≤Qm n) :
    (OriginalWorkingSubstitution.leg profile N : ℝ) ≤ 10^34*c*flight n := by
  have hv : (barge N).vol ≤ 8*n := by
    have hh := (barge_spec N (by omega)).upper
    omega
  have hv' : ((barge N).vol : ℝ) ≤ 8*n := by exact_mod_cast hv
  have hw := weighted_profile_lim hd hmono n N hn h hk ht hu
  have hscore := score_lim n N hn h hk ht hu
  unfold OriginalWorkingSubstitution.leg
  push_cast
  calc
    _ = (barge N).vol*((score (orderE N) : ℝ)+1)*
        ((profile (barge N).l : ℝ)+1) := by ring
    _ ≤ (8*n)*(10^32*(Qm n)^2)*((profile (barge N).l : ℝ)+1) := by
      gcongr
    _ = (8*n)*10^32*((Qm n)^2*((profile (barge N).l : ℝ)+1)) := by ring
    _ ≤ (8*n)*10^32*(4*c*Real.sqrt (Tm n)) := by
      exact mul_le_mul_of_nonneg_left hw (by positivity)
    _ = (32*10^32)*c*flight n := by unfold flight; ring
    _ ≤ _ := by
      have hc := hd.1
      unfold flight
      gcongr
      norm_num

theorem flight_big (n : ℕ) (ht : 1≤Tm n) : (n : ℝ) ≤ flight n := by
  have H : 1≤Real.sqrt (Tm n) := Real.one_le_sqrt.mpr ht
  unfold flight
  simpa using mul_le_mul_of_nonneg_left H (show 0≤(n : ℝ) by positivity)

/-- Preparation is polynomial in `stackN`, and the direct fallback disappears
eventually by the actual `Ports` estimate. This applies also to the upstream
chirp length maps between `n` and `2*n`. -/
theorem wind_ev {profile : ℕ → ℕ} {c : ℝ} {N : ℕ → ℕ}
    (hd : SqrtLogProfile profile c) (hmono : Monotone profile)
    (h : ∀ n : ℕ, n≤N n ∧ N n≤2*n) (d : ℕ) :
    ∀ᶠ n in atTop,
      (OriginalAllLengthSubstitution.fairwind profile d (N n) : ℝ)+1 ≤
        (10^34*c+4)*flight n := by
  filter_upwards [docks_ev h,polylog_ev h d,eventually_gt_atTop 0,
    Ttop.eventually_ge_atTop 1,Qtop.eventually_ge_atTop 1] with n hh hk hn ht hu
  unfold OriginalAllLengthSubstitution.fairwind
    OriginalArbitraryLengthSubstitution.Bench.surf
  rw [if_pos hh,Nat.add_zero]
  push_cast
  have hp := leg_lim hd hmono n (N n) hn (h n).1 (h n).2 ht hu
  have he := flight_big n ht
  have he' : 1≤(n : ℝ) := by exact_mod_cast hn
  have hx : (N n : ℝ) ≤ 2*n := by exact_mod_cast (h n).2
  linarith

theorem fairwind_bigO {profile : ℕ → ℕ} {c : ℝ}
    (hd : SqrtLogProfile profile c) (hmono : Monotone profile) (d : ℕ) :
    (fun n : ℕ => (OriginalAllLengthSubstitution.fairwind profile d n : ℝ)+1)
      =O[atTop] flight := by
  refine isBigO_iff.mpr ⟨10^34*c+4,?_⟩
  filter_upwards [wind_ev hd hmono (N:=id) (fun n => ⟨le_rfl,by simp only [id_eq]; omega⟩) d]
    with n hh
  rw [Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (by unfold flight; positivity)]
  exact hh

/-- One actual program handles all positive lengths, including its direct
fallback. The displayed work is `O(n sqrt(log n))`; every integer register
and offset still has the original polynomial cap. Both executors are genuine
complete uniform `Can` certificates, not coefficient or correctness oracles. -/
theorem executeOne_sqrtLog {profile : ℕ → ℕ} {c : ℝ}
    (hExec : SuppliedTensorExecutor sc parentRoot .left false profile)
    (hScalar : SuppliedTensorExecutor sc parentRoot .scalar false profile)
    (hmono : Monotone profile) (hd : SqrtLogProfile profile c) :
    ∃ (program : Prog false dftInKind dftOutKind) (d C p : ℕ),
      (∀ (n : ℕ), 0<n → ∀ x : Vec n,
        (run program (n,root (receipt n),(⟨n,x⟩ : Tape ℂ))).OK
          (⟨n,dft n x⟩ : Tape ℂ)
          (C*(OriginalAllLengthSubstitution.fairwind profile d n+1)) ((n+2)^p)) ∧
      (fun n : ℕ => ((C*(OriginalAllLengthSubstitution.fairwind profile d n+1) : ℕ) : ℝ))
        =O[atTop] flight := by
  obtain ⟨program,d,C,p,hp⟩ :=
    OriginalAllLengthSubstitution.executeOne_supplied hExec hScalar hmono
  refine ⟨program,d,C,p,hp,?_⟩
  refine isBigO_iff.mpr ⟨(C : ℝ)*(10^34*c+4),?_⟩
  filter_upwards [wind_ev hd hmono (N:=id) (fun n => ⟨le_rfl,by simp only [id_eq]; omega⟩) d]
    with n hh
  rw [Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (by unfold flight; positivity)]
  push_cast
  calc
    _ ≤ (C : ℝ)*((10^34*c+4)*flight n) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

end
end FourierSchur.OriginalSchurDensitySufficiency
