import vendor.OpenAIUniformFourierBundle
import MyProject.ToeplitzSuppliedRoots

/-! The supplied all-length Fourier root already provides the parent root
needed by the Schur Toeplitz circuits.  This file identifies its retained
halo register and the existing square-chain preparation.  It does not assert
a uniform RAM implementation of the Schur circuit or its coefficient tables. -/
namespace FourierSchur.OriginalCompilerRootBridge
open ToeplitzSuppliedRoots
open OAI.PowerSaving.Selection OAI.PowerSaving.RAM.Bench
noncomputable section

def capacity (k : Nat) : Nat := (k+1)^2

theorem capacity_le_harvest (n k : Nat) (hn : 0<n)
    (hk : k ≤ (barge n).l) : capacity k ≤ 2*harvestN n := by
  have hcount := (barge_spec n hn).count
  have hsmall : k+1 ≤ stackN n+1 := by omega
  have hlarge : stackN n+1 ≤ 16*(stackN n+4) := by omega
  change (k+1)^2 ≤ 2*(16*(stackN n+4))^2
  calc
    (k+1)^2 ≤ (stackN n+1)^2 := by gcongr
    _ ≤ (16*(stackN n+4))^2 := by gcongr
    _ ≤ 2*(16*(stackN n+4))^2 := by omega

theorem parentExponent_le_order (n k : Nat) (hn : 0<n)
    (hk : k ≤ (barge n).l) : parentExponent (capacity k) ≤ orderE n := by
  change Nat.log2 (capacity k)+2 ≤ Nat.log 2 (2*harvestN n)+2
  rw [Nat.log2_eq_log_two]
  exact Nat.add_le_add_right (Nat.log_mono_right (capacity_le_harvest n k hn hk)) 2

def parentRoot (k : Nat) : ℂ :=
  OAI.PowerSaving.root (2^(parentExponent (capacity k)))

theorem parentRoot_primitive (k : Nat) :
    IsPrimitiveRoot (parentRoot k) (2^(parentExponent (capacity k))) := by
  exact OAI.PowerSaving.Spectral.root_primitive _ (by positivity)

/-- The fifth field of the materialized forge contains the dyadic halos. -/
theorem forge_parentRoot (l e k : Nat) (r : OAI.PowerSaving.Grove.Axes) (z : ℂ)
    (he : parentExponent (capacity k) ≤ e) :
    ((forge l e r z).snd.snd.snd.snd.fst).look
      (parentExponent (capacity k)) 0 = parentRoot k := by
  change (OAI.PowerSaving.Tape.tab (e+1) halos).look
    (parentExponent (capacity k)) 0 = parentRoot k
  rw [OAI.PowerSaving.Tape.look_tab,
    if_pos (show parentExponent (capacity k)<e+1 by omega)]
  rfl

theorem working_forge_parentRoot (n k : Nat) (z : ℂ) (hn : 0<n)
    (hk : k ≤ (barge n).l) :
    ((forge (barge n).l (orderE n) (barge n).q z).snd.snd.snd.snd.fst).look
      (parentExponent (capacity k)) 0 = parentRoot k :=
  forge_parentRoot _ _ _ _ _ (parentExponent_le_order n k hn hk)

def roots (k : Nat) : RootFamily (capacity k) :=
  family (capacity k) (parentRoot k) (parentRoot_primitive k)

theorem roots_value (k : Nat) (m : Fin (capacity k+1)) (hm : 50 ≤ m.val) :
    (roots k m hm).val = (parentRoot k)^(2^(parentExponent (capacity k)-
      (ToeplitzChunkSize.selected m.val hm+2))) :=
  family_value (capacity k) (parentRoot k) (parentRoot_primitive k) m hm

theorem roots_primitive (k : Nat) (m : Fin (capacity k+1)) (hm : 50 ≤ m.val) :
    IsPrimitiveRoot (roots k m hm).val
      (2^(ToeplitzChunkSize.selected m.val hm+2)) :=
  (roots k m hm).property

theorem preparation_operations (k : Nat) :
    ConstantPreparation.operations (prepare (capacity k)) =
      parentExponent (capacity k) :=
  prepare_operations (capacity k)

theorem preparation_value (k : Nat) (m : Node (capacity k)) :
    ConstantPreparation.run (prepare (capacity k)) (fun _ => parentRoot k) m =
      (parentRoot k)^(2^(parentExponent (capacity k)-nodeExponent m)) :=
  prepare_correct (capacity k) (parentRoot k) m

theorem preparation_safe (k : Nat) :
    ConstantPreparation.DenominatorsNonzero (prepare (capacity k))
      (fun _ => parentRoot k) :=
  prepare_safe (capacity k) (fun _ => parentRoot k)

end
end FourierSchur.OriginalCompilerRootBridge
