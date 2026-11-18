import MyProject.ConstantPreparationCombinators
import MyProject.ToeplitzChunkSize
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Data.List.OfFn

/-! A finite preparation DAG derives every root used below a fixed parent
width from one supplied primitive root.  Each new register is the square
of the preceding register, and all earlier registers remain available. -/
namespace FourierSchur.ToeplitzSuppliedRoots
open ConstantPreparation
noncomputable section

def squareStep (d : Nat) : Tape (Fin (d+1)) (Fin (d+2)) :=
  .mul (Fin.last d) (Fin.last d) (.done (Fin.lastCases none Option.some))

theorem squareStep_last (d : Nat) (x : Fin (d+1) → ℂ) :
    run (squareStep d) x (Fin.last (d+1))=x (Fin.last d)*x (Fin.last d) := by
  simp only [squareStep,run,Fin.lastCases_last,Function.comp_apply,extend,Option.elim_none]

theorem squareStep_old (d : Nat) (x : Fin (d+1) → ℂ) (i : Fin (d+1)) :
    run (squareStep d) x i.castSucc=x i := by
  simp only [squareStep,run,Fin.lastCases_castSucc,Function.comp_apply,extend,Option.elim_some]

theorem squareStep_operations (d : Nat) : operations (squareStep d)=1 := rfl

theorem squareStep_safe (d : Nat) (x : Fin (d+1) → ℂ) :
    DenominatorsNonzero (squareStep d) x := by trivial

def build : (d : Nat) → Tape Unit (Fin (d+1))
  | 0 => .done (fun _ => ())
  | d+1 => compose (build d) (squareStep d)

theorem build_correct (d : Nat) (ζ : ℂ) (i : Fin (d+1)) :
    run (build d) (fun _ => ζ) i=ζ^(2^i.val) := by
  induction d with
  | zero => simp [build,run]
  | succ d ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [build,compose_correct,squareStep_last]
      simp only [ih,Fin.val_last,pow_succ]
      rw [pow_mul,pow_two]
    · rw [build,compose_correct,squareStep_old,ih]
      rfl

theorem build_operations (d : Nat) : operations (build d)=d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [build,compose_operations,ih,squareStep_operations]

theorem build_safe (d : Nat) (x : Unit → ℂ) :
    DenominatorsNonzero (build d) x := by
  induction d with
  | zero => trivial
  | succ d ih =>
    rw [build,compose_safe]
    exact ⟨ih,squareStep_safe d _⟩

def powersList (d : Nat) (ζ : ℂ) : List ℂ :=
  List.ofFn (run (build d) (fun _ => ζ))

theorem powersList_length (d : Nat) (ζ : ℂ) : (powersList d ζ).length=d+1 := by
  simp only [powersList,List.length_ofFn]

theorem powersList_values (d : Nat) (ζ : ℂ) :
    powersList d ζ=List.ofFn (fun i : Fin (d+1) => ζ^(2^i.val)) := by
  unfold powersList
  congr 1
  funext i
  exact build_correct d ζ i

def derived (ζ : ℂ) (D E : Nat) : ℂ := ζ^(2^(D-E))

theorem derived_primitive (ζ : ℂ) (D E : Nat) (hE : E ≤ D)
    (hζ : IsPrimitiveRoot ζ (2^D)) : IsPrimitiveRoot (derived ζ D E) (2^E) := by
  have hproduct : (2^D : Nat)=2^(D-E)*2^E := by
    rw [← pow_add,Nat.sub_add_cancel hE]
  exact IsPrimitiveRoot.pow (by positivity) hζ hproduct

def parentExponent (n : Nat) : Nat := Nat.log2 n+2

abbrev Node (n : Nat) := {m : Fin (n+1) // 50 ≤ m.val}

def nodeExponent {n : Nat} (m : Node n) : Nat :=
  ToeplitzChunkSize.selected m.val.val m.property+2

theorem nodeExponent_le {n : Nat} (m : Node n) : nodeExponent m ≤ parentExponent n := by
  have hm : m.val.val ≤ n := by have hi := m.val.isLt; omega
  have hs := ToeplitzChunkSize.selected_log_bound m.val.val m.property
  have hl : Nat.log 2 m.val.val ≤ Nat.log 2 n := Nat.log_mono_right hm
  simp only [nodeExponent,parentExponent,Nat.log2_eq_log_two]
  omega

def rootPort {n : Nat} (m : Node n) : Fin (parentExponent n+1) :=
  ⟨parentExponent n-nodeExponent m,by omega⟩

/-- The output wiring selects an already retained power register.  It
performs no additional arithmetic, even when several nodes share a root. -/
def prepare (n : Nat) : Tape Unit (Node n) :=
  compose (build (parentExponent n)) (.done rootPort)

theorem prepare_correct (n : Nat) (ζ : ℂ) (m : Node n) :
    run (prepare n) (fun _ => ζ) m=derived ζ (parentExponent n) (nodeExponent m) := by
  rw [prepare,compose_correct]
  change run (build (parentExponent n)) (fun _ => ζ) (rootPort m)=_
  rw [build_correct]
  rfl

theorem prepare_operations (n : Nat) : operations (prepare n)=Nat.log2 n+2 := by
  rw [prepare,compose_operations,build_operations]
  rfl

theorem prepare_safe (n : Nat) (x : Unit → ℂ) : DenominatorsNonzero (prepare n) x := by
  rw [prepare,compose_safe]
  exact ⟨build_safe _ x,by trivial⟩

theorem prepared_primitive (n : Nat) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (2^(parentExponent n))) (m : Node n) :
    IsPrimitiveRoot (run (prepare n) (fun _ => ζ) m) (2^(nodeExponent m)) := by
  rw [prepare_correct]
  exact derived_primitive ζ (parentExponent n) (nodeExponent m) (nodeExponent_le m) hζ

abbrev RootFamily (n : Nat) := (m : Fin (n+1)) → (hm : 50 ≤ m.val) →
  {ζ : ℂ // IsPrimitiveRoot ζ (2^(ToeplitzChunkSize.selected m.val hm+2))}

def family (n : Nat) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2^(parentExponent n))) :
    RootFamily n := fun m hm =>
  ⟨run (prepare n) (fun _ => ζ) ⟨m,hm⟩,prepared_primitive n ζ hζ ⟨m,hm⟩⟩

theorem family_value (n : Nat) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (2^(parentExponent n))) (m : Fin (n+1))
    (hm : 50 ≤ m.val) :
    (family n ζ hζ m hm).val=ζ^(2^(parentExponent n-
      (ToeplitzChunkSize.selected m.val hm+2))) :=
  prepare_correct n ζ ⟨m,hm⟩

end
end FourierSchur.ToeplitzSuppliedRoots
