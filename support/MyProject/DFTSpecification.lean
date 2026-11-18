import MyProject.LinearCircuit
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! The full complex DFT and a precise scalar-gate target.
No fast compiler is asserted to exist here. The target is a proposition,
not an axiom, and has not been proved. Uniform construction and the costs
of preparing coefficients and routing require additional certificates. -/
namespace FourierSchur.DFT
open Filter Asymptotics
open LinearCircuit

noncomputable section

def transform (n : Nat) (ω : ℂ) (x : Fin n → ℂ) (k : Fin n) : ℂ :=
  ∑ j : Fin n, ω ^ (j.val * k.val) * x j

def SqrtLogGateClaim : Prop :=
  ∃ (cost : Nat → ℝ),
    (cost =O[atTop] fun n : Nat => (n : ℝ) * Real.sqrt (Real.log ((n : ℝ)+2))) ∧
    ∀ (n : Nat), 0 < n → ∀ ω : ℂ, IsPrimitiveRoot ω n →
      ∃ p : Program ℂ n n, Computes p (transform n ω) ∧ (gates p : ℝ) ≤ cost n

/-- A complete complex baseline, charged one multiply and one add per term. -/
abbrev RowInstruction (n : Nat) := Fin n × ℂ

def executeRow {n : Nat} : List (RowInstruction n) → (Fin n → ℂ) → ℂ
  | [], _ => 0
  | (j,c) :: rest, x => c * x j + executeRow rest x

def denseRow (n : Nat) (ω : ℂ) (k : Fin n) : List (RowInstruction n) :=
  (List.finRange n).map (fun j => (j, ω ^ (j.val * k.val)))

theorem executeRow_sum {n : Nat} (row : List (RowInstruction n)) (x : Fin n → ℂ) :
    executeRow row x = (row.map (fun term => term.2 * x term.1)).sum := by
  induction row with
  | nil => rfl
  | cons term rest ih => cases term; simp [executeRow, ih]

theorem denseRow_correct (n : Nat) (ω : ℂ) (x : Fin n → ℂ) (k : Fin n) :
    executeRow (denseRow n ω k) x = transform n ω x k := by
  rw [executeRow_sum]
  simp [denseRow, transform, Function.comp_def,
    List.sum_ofFn, List.finRange]

def denseScalarGates (n : Nat) (ω : ℂ) : Nat :=
  ∑ k : Fin n, 2 * (denseRow n ω k).length

theorem denseScalarGates_exact (n : Nat) (ω : ℂ) :
    denseScalarGates n ω = 2*n*n := by
  simp [denseScalarGates, denseRow]
  ring

/-- The complex DFT is linear on arbitrary input data. -/
theorem transform_add (n : Nat) (ω : ℂ) (x y : Fin n → ℂ) :
    transform n ω (x+y) = transform n ω x + transform n ω y := by
  funext k
  simp [transform, mul_add, Finset.sum_add_distrib]

theorem transform_scale (n : Nat) (ω c : ℂ) (x : Fin n → ℂ) :
    transform n ω (fun j => c*x j) = fun k => c * transform n ω x k := by
  funext k
  simp only [transform, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end FourierSchur.DFT
