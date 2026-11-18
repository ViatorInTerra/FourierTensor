import MyProject.DFTSpecification

/-! Circuit composition for the Schur conjugation identity.
The existence of the analysis, block-action, synthesis circuits and their
intertwining identity are explicit hypotheses, not axioms. -/
namespace FourierSchur
open LinearCircuit
noncomputable section

def bitIndex {d : Nat} (i : Fin (2^d)) (t : Fin d) : Fin 2 :=
  ⟨(i.val / 2^t.val) % 2, Nat.mod_lt _ (by decide)⟩

/-- Full Kronecker power, with natural binary coordinate indexing. -/
def tensorAction (d : Nat) (A : Fin 2 → Fin 2 → ℂ)
    (x : Fin (2^d) → ℂ) (i : Fin (2^d)) : ℂ :=
  ∑ j : Fin (2^d), (∏ t : Fin d, A (bitIndex i t) (bitIndex j t)) * x j

def fourierKernel (i j : Fin 2) : ℂ :=
  if i = j then (1+Complex.I)/2 else (1-Complex.I)/2

def TensorGateClaim : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ d : Nat,
    ∃ p : Program ℂ (2^d) (2^d),
      Computes p (tensorAction d fourierKernel) ∧
      (gates p : ℝ) ≤ c * (2:ℝ)^d *
        (1 + (Real.log ((d:ℝ)+2))^3 * Real.log (Real.log ((d:ℝ)+3)))

def schurProgram {n : Nat} (analysis blocks synthesis : Program ℂ n n) :
    Program ℂ n n := compose (compose analysis blocks) synthesis

/-- The actual DAG computes the tensor action when the Schur identity and
the three constituent programs are supplied. It computes every output on
every input, and charges all three phases. -/
theorem schurProgram_correct {n : Nat}
    (analysis blocks synthesis : Program ℂ n n)
    (S B T target : (Fin n → ℂ) → (Fin n → ℂ))
    (hS : Computes analysis S) (hB : Computes blocks B) (hT : Computes synthesis T)
    (hintertwine : ∀ x, T (B (S x)) = target x) :
    Computes (schurProgram analysis blocks synthesis) target ∧
      gates (schurProgram analysis blocks synthesis) =
        gates analysis + gates blocks + gates synthesis := by
  constructor
  · intro x
    simp only [schurProgram, then_correct]
    rw [hS, hB, hT]
    exact hintertwine x
  · simp [schurProgram, then_gates]

theorem schurProgram_bound {n : Nat}
    (analysis blocks synthesis : Program ℂ n n) (a b c : Nat)
    (ha : gates analysis ≤ a) (hb : gates blocks ≤ b) (hc : gates synthesis ≤ c) :
    gates (schurProgram analysis blocks synthesis) ≤ a+b+c := by
  simp only [schurProgram, then_gates]
  omega

end
end FourierSchur
