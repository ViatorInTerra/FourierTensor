import work_in_progress.OriginalProjectionNativeRowCertificate
import work_in_progress.OriginalNativeGeneratorRealization

/-! The actual 65 native symbol generators used by the full printed DAG.
The zero generator is the complete 125-coordinate kernel; the other
generators are the concrete checked orthonormal line frames.
-/
namespace FourierSchur.OriginalProjectionNativeGenerators
open OAI.PowerSaving OAI.PowerSaving.Binary Matrix Finset
open OriginalBinaryMatrixCertificates OriginalCheckedNativeDirection
open OriginalNativeGeneratorSymbols OriginalNativeGeneratorRealization
open OriginalProjectionNativeRowCertificate
noncomputable section
set_option maxRecDepth 20000

def generators (i : Fin 65) (x : Space (Fin 125)) : ℂ :=
  if i=0 then lum x else lineSymbol (wordVector 125 (directions i)) x

theorem direction_zero : directions 0=2^125-1 := by decide

theorem directions_unit : ∀ i : Fin 65,
    i=0 ∨ fastDot 125 (directions i) (directions i)=1 := by decide

theorem generators_square (i : Fin 65) (x : Space (Fin 125)) :
    generators i x*generators i x=character 125 (directions i) x := by
  by_cases h : i=0
  · subst i
    simp only [generators,if_pos rfl,direction_zero]
    exact full_square 125 x
  · simp only [generators,if_neg h]
    exact line_square (directions i) (checked_self _ _ ((directions_unit i).resolve_left h)) x

theorem full_operator : operator generators ⟨1,0⟩=kernel (Fin 125) := by
  have h := operator_generator generators (0 : Fin 65)
  simp only [Fin.val_zero,Nat.pow_zero] at h
  rw [h]
  have hg : generators 0=lum := by funext x; simp [generators]
  rw [hg,wrap_lum]

theorem line_operator (i : Fin 65) (hi : i≠0) :
    operator generators ⟨2^i.val,0⟩=delta (wordVector 125 (directions i)) := by
  rw [operator_generator generators i]
  congr 1
  funext x
  simp only [generators,if_neg hi,OriginalNativeGeneratorRealization.lineSymbol]

end
end FourierSchur.OriginalProjectionNativeGenerators
