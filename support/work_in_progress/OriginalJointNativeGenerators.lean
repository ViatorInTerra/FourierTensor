import work_in_progress.OriginalJointNativeRowCertificate
import work_in_progress.OriginalNativeGeneratorRealization

/-! The actual 47 native symbol generators used by the full printed DAG.
The zero generator is the complete 216-coordinate kernel; the other
generators are the concrete checked orthonormal line frames.
-/
namespace FourierSchur.OriginalJointNativeGenerators
open OAI.PowerSaving OAI.PowerSaving.Binary Matrix Finset
open OriginalBinaryMatrixCertificates OriginalCheckedNativeDirection
open OriginalNativeGeneratorSymbols OriginalNativeGeneratorRealization
open OriginalJointNativeRowCertificate
noncomputable section
set_option maxRecDepth 20000

def generators (i : Fin 47) (x : Space (Fin 216)) : ℂ :=
  if i=0 then lum x else lineSymbol (wordVector 216 (directions i)) x

theorem direction_zero : directions 0=2^216-1 := by decide

theorem directions_unit : ∀ i : Fin 47,
    i=0 ∨ fastDot 216 (directions i) (directions i)=1 := by decide

theorem generators_square (i : Fin 47) (x : Space (Fin 216)) :
    generators i x*generators i x=character 216 (directions i) x := by
  by_cases h : i=0
  · subst i
    simp only [generators,if_pos rfl,direction_zero]
    exact full_square 216 x
  · simp only [generators,if_neg h]
    exact line_square (directions i) (checked_self _ _ ((directions_unit i).resolve_left h)) x

theorem full_operator : operator generators ⟨1,0⟩=kernel (Fin 216) := by
  have h := operator_generator generators (0 : Fin 47)
  simp only [Fin.val_zero,Nat.pow_zero] at h
  rw [h]
  have hg : generators 0=lum := by funext x; simp [generators]
  rw [hg,wrap_lum]

theorem line_operator (i : Fin 47) (hi : i≠0) :
    operator generators ⟨2^i.val,0⟩=delta (wordVector 216 (directions i)) := by
  rw [operator_generator generators i]
  congr 1
  funext x
  simp only [generators,if_neg hi,OriginalNativeGeneratorRealization.lineSymbol]

end
end FourierSchur.OriginalJointNativeGenerators
