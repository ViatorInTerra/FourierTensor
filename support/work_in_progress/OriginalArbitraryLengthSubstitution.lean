import work_in_progress.OriginalWorkingSubstitution

/-! The original working-length chirp path with a replaceable supplied
complete tensor executor. Every convolution transform uses the proved paid
parent-root preparation boundary. All scalar powers, array work, input
padding and final chirp extraction retain their original RAM charges.
This covers the `Ports` branch and does not instantiate a fast density. -/
namespace FourierSchur.OriginalArbitraryLengthSubstitution
open OAI.PowerSaving OAI.PowerSaving.Selection OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty OAI.PowerSaving.RAM.Bench
open Spectral
open OriginalCompilerRootBridge OriginalSectorSubstitution
noncomputable section
universe U
namespace Bench
variable {ι : Type U} {m : Bool} {b : OAI.PowerSaving.RAM.Bench m ι}
  {s t : Ty} {S n N : ι → ℕ} {profile : ℕ → ℕ} {cl : Paint}

def surf (profile : ℕ → ℕ) (d n s : ℕ) : ℕ :=
  n+OriginalWorkingSubstitution.leg profile n+(s+2)^d
lemma surf_deg (s n : ℕ) {c d : ℕ} (h : c≤d) : surf profile c n s ≤ surf profile d n s :=
  Nat.add_le_add_left (Small.pow_mono_degree _ h) _

def Swift (profile : ℕ → ℕ) (b : OAI.PowerSaving.RAM.Bench m ι)
    (n S : ι → ℕ) (t : Ty) (x : ι → T t) : Prop :=
  ∃ d : ℕ, b.Moves (fun i => surf profile d (n i) (S i)) t x

namespace Swift
variable {x y : ι→T t}
lemma of_moves {W} (h : b.Moves W t x) (g : Dom n W) :
    Swift profile b n S t x :=
  ⟨0,h.weaken ((Dom.of_le fun i => by unfold surf; omega).trans g)⟩
lemma of_dry (h : b.Dry S t x) : Swift profile b n S t x :=
  let ⟨d,hd⟩ := h
  ⟨d, hd.mono fun _ => Nat.le_add_left _ _⟩
lemma pair {v : ι→T s} (h : Swift profile b n S t x) (g : Swift profile b n S s v) :
    Swift profile b n S (p t s) fun i => (x i,v i) :=
  let ⟨d,hd⟩ := h
  let ⟨l,hl⟩ := g
  ⟨d+l, (hd.weaken (Dom.of_le fun i => surf_deg (profile:=profile) (S i) (n i) (by omega))).pair
    (hl.weaken (Dom.of_le fun i => surf_deg (profile:=profile) (S i) (n i) (by omega)))⟩
lemma bind {v : ι→T s} (h : Swift profile b n S t x) (g : Swift profile (b.extend t x) n S s v) :
    Swift profile b n S s v :=
  let ⟨d,hd⟩ := h
  let ⟨l,hl⟩ := g
  ⟨d+l, caseM (hd.weaken (Dom.of_le fun i => surf_deg (profile:=profile) (S i) (n i) (by omega)))
    (hl.weaken (Dom.of_le fun i => surf_deg (profile:=profile) (S i) (n i) (by omega)))⟩
end Swift

namespace Cruise
variable {x y : ι → Line}

lemma flood (hExec : SuppliedTensorExecutor sc parentRoot cl m profile) (hmono : Monotone profile) (h : b.Cruise n S N) (r : Bool)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (N i) (x i)) :
    Swift profile b n S (a (c cl)) fun i => Tape.tab (N i) (freq (N i) (pr r (N i)) (x i)) := by
  let z (i) := pr r (N i)
  have H (i) : (barge (n i)).vol=N i := h.ac i
  have hu := signP r h.volume_pos ((h.dims.mediumP h.port h.rootP).congr fun i =>
    congrArg root (H i))
  obtain ⟨d,hd⟩ := OriginalWorkingSubstitution.streamP_supplied hExec hmono h.dims h.port h.rootP (z:=z) (x:=x) hu
    (fun i => (H i).symm ▸ show IsPrimitiveRoot (z i) (N i) from primitive_pr _ (h.volume_pos i) r)
    (hx.congr fun i => congrArg (fun u => Tape.tab u (x i)) (H i).symm)
  refine ⟨d,?_⟩
  refine (hd.weaken (Dom.of_le fun i => ?_)).congr fun i => ?_
  · unfold surf; omega
  · rw [H]

lemma flood' (hExec : SuppliedTensorExecutor sc parentRoot cl m profile) (hmono : Monotone profile) (h : b.Cruise n S N) (r : Bool) (hx : Swift profile b n S (a (c cl)) fun i =>
    Tape.tab (N i) (x i)) :
    Swift profile b n S (a (c cl)) fun i => Tape.tab (N i) (freq (N i) (pr r (N i)) (x i)) := by
  let V (i : ι) : T (a (c cl)) := Tape.tab (N i) (x i)
  exact hx.bind (flood hExec hmono (h.transfer (Instant.extend b V)) r (x:=x) (cherry b V (t:=a (c cl))))

lemma posts (h : b.Cruise n S N) (r : Bool) :
    Swift profile b n S (a sc) fun i => tablePow (pr r (2*n i)) (S i) := by
  let z (i) : T sc := pr r (2*n i)
  have hh : Swift profile b n S sc z :=
    Swift.of_dry (signP r (fun i => by have := h.dims.pos i; omega)
      (h.dims.etaP h.port h.rootP))
  have F := Instant.extend b z (t:=sc)
  exact hh.bind (Swift.of_moves (pylon (h.dims.tidal.transfer F)
    (g:=h.dims.stackPow) (cherry b z (t:=sc))) ⟨4,fun i => by
    dsimp only [id]
    have hh : 2^S i ≤ 4*n i := h.dims.stack_eq i ▸ stack_pow (n i) (h.dims.pos i); omega⟩)

lemma pearl (h : b.Cruise n S N) (r : Bool)
    (hp : b.Moves (fun _ => 0) (a sc) fun i => tablePow (pr r (2*n i)) (S i))
    {k} (hk : b.Nick k) :
    b.Moves (fun _ => 0) sc fun i => epschirp (pr r (2*n i)) (k i) :=
  square_pow h.dims.stackPow hp ((Nick.wc 2).mul h.dims.num)
    (fun i => ⟨by have := h.dims.pos i; omega,h.dims.stack_eq i ▸ (stack_above (n i)).le⟩)
    (fun i => (primitive_pr (2*n i) (by have := h.dims.pos i; omega) r).pow_eq_one) hk

-- two prep arrays
lemma risen (h : b.Cruise n S N) (r : Bool)
    (hp : b.Moves (fun _ => 0) (a sc) fun i => tablePow (pr r (2*n i)) (S i))
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (n i) (x i)) :
    Swift profile b n S (a (c cl)) fun i => Tape.tab (N i) (chirp_seed (n i) (pr r (2*n i)) (x i)) := by
  have F := Instant.scan b N
  have hh := h.transfer F
  have hj := chop h.sizeL
  have H := (hh.pearl r (hp.transfer F) hj).mul (pick_all (t:=c cl)
    (n:=fun i : During N => n i.i) (fun (i : During N) j => x i.i j) (hx.transfer F) hj)
  refine Swift.of_moves (arrayNow h.sizeL _ (H.congr fun i => ?_)) h.dom
  simp only [chirp_seed,mul_ite]; congr 1
  exact mul_zero _

lemma fallen (h : b.Cruise n S N) (r : Bool)
    (hp : b.Moves (fun _ => 0) (a sc) fun i => tablePow (pr r (2*n i)) (S i)) :
    Swift profile b n S (a sc) fun i => Tape.tab (N i) (fall (n i) (N i) (pr r (2*n i))) := by
  let z i := pr r (2*n i)
  have F := Instant.scan b N
  have hh := h.transfer F
  have hj := chop h.sizeL
  have hg := hh.sizeL.sub hj
  have hk := (((hj.cmp hh.dims.num).branch hg hj)).congr
    (y:=fun i => legdist (n i.i) (N i.i) i.j) (fun i => by
    by_cases e : i.j < n i.i <;> simp [legdist,e])
  refine Swift.of_moves (arrayNow h.sizeL _ ((hh.pearl r (hp.transfer F) hk).inv fun i => ?_)) h.dom
  have Hu : 0<2*n i.i := by have := h.dims.pos i.i; omega
  exact pow_ne_zero _ ((primitive_pr _ Hu r).ne_zero (Nat.ne_of_gt Hu))

lemma pyramid (hExec : SuppliedTensorExecutor sc parentRoot cl m profile)
    (hScalar : SuppliedTensorExecutor sc parentRoot .scalar m profile) (hmono : Monotone profile) (h : b.Cruise n S N) (r : Bool)
    (hp : b.Moves (fun _ => 0) (a sc) fun i => tablePow (pr r (2*n i)) (S i))
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (n i) (x i)) :
    Swift profile b n S (a (c cl)) fun i =>
      Tape.tab (N i) (fetchC (N i) (pr false (N i))
        (fall (n i) (N i) (pr r (2*n i)))
        (chirp_seed (n i) (pr r (2*n i)) (x i))) := by
  let z i := pr r (2*n i)
  let A i := freq (N i) (pr false (N i)) (fall (n i) (N i) (z i))
  let B i := freq (N i) (pr false (N i)) (chirp_seed (n i) (z i) (x i))
  let V (i) : T (p (a sc) (a (c cl))) := (Tape.tab (N i) (A i),Tape.tab (N i) (B i))
  have H := (flood' hScalar hmono h false (fallen h r hp)).pair (flood' hExec hmono h false (risen h r hp hx))
  have F := Instant.extend b V
  have hk := cherry b V (W:=fun _ => 0)
  exact flood' hExec hmono h true (x:=fun i => pointC (N i) (pr false (N i))
        (fall (n i) (N i) (z i)) (chirp_seed (n i) (z i) (x i)))
    (H.bind (Swift.of_moves (table_scale (h.sizeL.transfer F) (x:=A) (y:=B) hk.fst hk.snd) h.dom))

lemma singing (hExec : SuppliedTensorExecutor sc parentRoot cl m profile)
    (hScalar : SuppliedTensorExecutor sc parentRoot .scalar m profile) (hmono : Monotone profile) (h : b.Cruise n S N) (r : Bool)
    (hp : b.Moves (fun _ => 0) (a sc) fun i => tablePow (pr r (2*n i)) (S i))
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (n i) (x i)) :
    Swift profile b n S (a (c cl)) fun i =>
      Tape.tab (n i) (freq (n i) (pr r (n i)) (x i)) := by
  let z i := pr r (2*n i)
  let B i := fetchC (N i) (pr false (N i)) (fall (n i) (N i) (z i))
    (chirp_seed (n i) (z i) (x i))
  have H := Swift.pair (pyramid hExec hScalar hmono h r hp hx) (Swift.of_moves h.sizeL.numeralM h.dom)
  let V (i : ι) : T (p (a (c cl)) sc) := (Tape.tab (N i) (B i),(N i:ℂ))
  have F := Instant.extend b V
  have G := Instant.scan (b.extend _ V) n
  have hh := h.transfer (G.next F)
  have hk := Moves.transfer (cherry b V (W:=fun _ => 0)) G
  have hj := h.dims.num.transfer F
  have HL := chop hj
  have HS := Moves.pick (n:=fun i : During n => N i.i) (k:=During.j) (t:=c cl)
    (fun i => B i.i) hk.fst HL.close (fun i => by
      change i.j < N i.i
      have hh := h.volume_ge i.i; have hk := i.hj; omega)
  have hd := (hh.pearl r (hp.transfer (G.next F)) HL).mul
    ((hk.snd.inv fun i => Nat.cast_ne_zero.mpr (Nat.ne_of_gt (h.volume_pos i.i))).mul HS)
  exact H.bind (Swift.of_moves (arrayNow hj _ (hd.congr fun i =>
    chirps _ _ (h.dims.pos i.i) (h.volume_ge i.i) r _ _ i.hj)) (Dom.self n))

lemma deliver (hExec : SuppliedTensorExecutor sc parentRoot cl m profile)
    (hScalar : SuppliedTensorExecutor sc parentRoot .scalar m profile) (hmono : Monotone profile) (h : b.Cruise n S N) (r : Bool)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (n i) (x i)) :
    Swift profile b n S (a (c cl)) fun i =>
      Tape.tab (n i) (freq (n i) (pr r (n i)) (x i)) := by
  let V i := tablePow (pr r (2*n i)) (S i)
  have F := Instant.extend b V (t:=a sc)
  exact (posts h r).bind (singing hExec hScalar hmono (h.transfer F) r (cherry b V (t:=a sc)) (hx.transfer F))

end Cruise

lemma Neaps.swift_supplied (hExec : SuppliedTensorExecutor sc parentRoot cl m profile)
    (hScalar : SuppliedTensorExecutor sc parentRoot .scalar m profile) (hmono : Monotone profile) (h : b.Neaps S n) (g : ∀ i,Ports (n i))
    (hz : b.Dry S sc fun i => root (receipt (n i))) (r : Bool)
    {x : ι→Line} (hx : b.Moves (fun _ => 0) (a (c cl)) fun i =>
      Tape.tab (n i) (x i)) :
    Swift profile b n S (a (c cl)) fun i =>
      Tape.tab (n i) (freq (n i) (pr r (n i)) (x i)) := by
  let N i := tailVol (n i)
  have F := Instant.extend b N (t:=w)
  have hh : (b.extend w N).Cruise n S N :=
    ⟨h.transfer F,g,hz.transfer F,fun i => rfl,⟨cherry b N (t:=w),h.bargeL.volume⟩⟩
  exact (Swift.of_dry h.bargeL.volL.dry).bind (Cruise.deliver hExec hScalar hmono hh r (hx.transfer F))


end Bench
end
end FourierSchur.OriginalArbitraryLengthSubstitution
