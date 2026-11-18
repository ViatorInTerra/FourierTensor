import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-! A typed straight-line DAG, allowing shared intermediate registers.
Each instruction is one addition or multiplication by a fixed scalar.
Fan-out and output selection are free in the scalar-gate model; routing
and preparation need separate cost certificates for the uniform claim. -/
namespace FourierSchur.LinearCircuit

inductive Program (K : Type) : Nat → Nat → Type where
  | done {n m} (outputs : Fin m → Fin n) : Program K n m
  | add {n m} (a b : Fin n) (rest : Program K (n+1) m) : Program K n m
  | scale {n m} (c : K) (a : Fin n) (rest : Program K (n+1) m) : Program K n m

def gates {K : Type} {n m : Nat} : Program K n m → Nat
  | .done _ => 0
  | .add _ _ rest => 1 + gates rest
  | .scale _ _ rest => 1 + gates rest

def run {K : Type} [Add K] [Mul K] {n m : Nat} :
    Program K n m → (Fin n → K) → (Fin m → K)
  | .done outputs, x => fun i => x (outputs i)
  | .add a b rest, x => run rest (Fin.snoc x (x a + x b))
  | .scale c a rest, x => run rest (Fin.snoc x (c * x a))

def liftMap {n p : Nat} (f : Fin n → Fin p) : Fin (n+1) → Fin (p+1) :=
  Fin.lastCases (Fin.last p) (fun i => (f i).castSucc)

def rename {K : Type} {n m p : Nat} (f : Fin n → Fin p) :
    Program K n m → Program K p m
  | .done outputs => .done (f ∘ outputs)
  | .add a b rest => .add (f a) (f b) (rename (liftMap f) rest)
  | .scale c a rest => .scale c (f a) (rename (liftMap f) rest)

theorem snoc_liftMap {K : Type} {n p : Nat} (f : Fin n → Fin p)
    (x : Fin p → K) (v : K) :
    (Fin.snoc x v) ∘ liftMap f = Fin.snoc (x ∘ f) v := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [liftMap]
  | cast i => simp [liftMap]

theorem rename_correct {K : Type} [Add K] [Mul K] {n m p : Nat}
    (f : Fin n → Fin p) (program : Program K n m) (x : Fin p → K) :
    run (rename f program) x = run program (x ∘ f) := by
  induction program generalizing p with
  | done outputs => rfl
  | add a b rest ih =>
    simp only [rename, run]
    rw [ih, snoc_liftMap]
    rfl
  | scale c a rest ih =>
    simp only [rename, run]
    rw [ih, snoc_liftMap]
    rfl

theorem rename_gates {K : Type} {n m p : Nat} (f : Fin n → Fin p)
    (program : Program K n m) : gates (rename f program) = gates program := by
  induction program generalizing p with
  | done outputs => rfl
  | add a b rest ih => simp [rename, gates, ih]
  | scale c a rest ih => simp [rename, gates, ih]

/-- Execute p, then q, while retaining shared registers from p. -/
def compose {K : Type} {n m k : Nat} :
    Program K n m → Program K m k → Program K n k
  | .done outputs, q => rename outputs q
  | .add a b rest, q => .add a b (compose rest q)
  | .scale c a rest, q => .scale c a (compose rest q)

theorem then_correct {K : Type} [Add K] [Mul K] {n m k : Nat}
    (p : Program K n m) (q : Program K m k) (x : Fin n → K) :
    run (compose p q) x = run q (run p x) := by
  induction p with
  | done outputs => exact rename_correct outputs q x
  | add a b rest ih => exact ih q (Fin.snoc x (x a + x b))
  | scale c a rest ih => exact ih q (Fin.snoc x (c * x a))

theorem then_gates {K : Type} {n m k : Nat}
    (p : Program K n m) (q : Program K m k) :
    gates (compose p q) = gates p + gates q := by
  induction p with
  | done outputs => simp [compose, gates, rename_gates]
  | add a b rest ih => simp [compose, gates, ih, Nat.add_assoc]
  | scale c a rest ih => simp [compose, gates, ih, Nat.add_assoc]

/-- A semantic certificate is quantified over every input and every output. -/
def Computes {K : Type} [Add K] [Mul K] {n m : Nat}
    (p : Program K n m) (f : (Fin n → K) → (Fin m → K)) : Prop :=
  ∀ x, run p x = f x

theorem computes_then {K : Type} [Add K] [Mul K] {n m k : Nat}
    (p : Program K n m) (q : Program K m k)
    (f : (Fin n → K) → (Fin m → K)) (g : (Fin m → K) → (Fin k → K))
    (hp : Computes p f) (hq : Computes q g) : Computes (compose p q) (g ∘ f) := by
  intro x
  rw [then_correct, hp, hq]
  rfl

end FourierSchur.LinearCircuit

