import work_in_progress.OriginalProjectionNativeFrameDictionary

/-! The concrete empty/full/line/complement alphabet is exactly the
small symbol alphabet used by the complete output certificate. In
particular, a complement remains ONE native frame-service request.
-/
namespace FourierSchur.OriginalProjectionFrameAlphabet
open OAI.PowerSaving OAI.PowerSaving.Binary Matrix Finset
open OriginalNativeGeneratorSymbols OriginalNativeGeneratorRealization
open OriginalProjectionNativeGenerators OriginalProjectionNativeRowCertificate
open OriginalProjectionNativeFrameDictionary OriginalNativeComplementClosure
noncomputable section
set_option maxRecDepth 20000

inductive Mode where
  | empty
  | full
  | line (i : Fin 65)
  | complement (i : Fin 65)
  deriving DecidableEq, Repr

def admissible : Mode → Prop
  | .line i => i≠0
  | .complement i => i≠0
  | _ => True

instance (m : Mode) : Decidable (admissible m) := by cases m <;> unfold admissible <;> infer_instance

def generatorTag (i : Fin 65) : Tag := ⟨2^i.val,0⟩
def inverseTag (i : Fin 65) : Tag := ⟨2^i.val,directions i⟩

theorem inverse_tags : ∀ i : Fin 65,
    compose directions (inverseTag i) (generatorTag i)=unitTag := by decide +kernel

theorem unit_operator : operator generators unitTag=1 := by
  unfold operator
  have h : value generators unitTag=fun _ => 1 := funext (value_unit generators)
  rw [h,wrap_one]

theorem inverse_frame (i : Fin 65) (hi : i≠0) :
    operator generators (inverseTag i)=unframe (nativeBase i) {pivot i} := by
  have he : operator generators (inverseTag i)*frame (nativeBase i) {pivot i}=1 := by
    rw [frame_line i hi]
    change operator generators (inverseTag i)*operator generators (generatorTag i)=1
    rw [← operator_compose directions generators generators_square,inverse_tags i,unit_operator]
  calc
    _ = operator generators (inverseTag i)*
        (frame (nativeBase i) {pivot i}*unframe (nativeBase i) {pivot i}) := by
      rw [unframe_right,mul_one]
    _ = (operator generators (inverseTag i)*frame (nativeBase i) {pivot i})*
        unframe (nativeBase i) {pivot i} := by rw [Matrix.mul_assoc]
    _ = _ := by rw [he,one_mul]

def modeTag : Mode → Tag
  | .empty => unitTag
  | .full => ⟨1,0⟩
  | .line i => generatorTag i
  | .complement i => compose directions ⟨1,0⟩ (inverseTag i)

def modeBase : Mode → OBase (Fin 125)
  | .line i => nativeBase i
  | .complement i => nativeBase i
  | _ => OBase.canonical (Fin 125)

def modeMask : Mode → Finset (Fin 125)
  | .empty => ∅
  | .full => univ
  | .line i => {pivot i}
  | .complement i => univ\{pivot i}

theorem mode_operator (m : Mode) (hm : admissible m) :
    operator generators (modeTag m)=frame (modeBase m) (modeMask m) := by
  cases m with
  | empty => simp only [modeTag,modeBase,modeMask,unit_operator,frame_zero]
  | full => simp only [modeTag,modeBase,modeMask,full_operator,frame_univ]
  | line i => exact (frame_line i hm).symm
  | complement i =>
    simp only [modeTag,modeBase,modeMask]
    rw [operator_compose directions generators generators_square,full_operator,inverse_frame i hm]
    exact kernel_unframe (nativeBase i) {pivot i}

def nativeTag (m : Mode) (z : ℕ) : Tag := compose directions ⟨0,z⟩ (modeTag m)

theorem native_operator (m : Mode) (hm : admissible m) (z : ℕ) :
    operator generators (nativeTag m z)=
      shift (OriginalBinaryMatrixCertificates.wordVector 125 z)*frame (modeBase m) (modeMask m) := by
  rw [nativeTag,operator_compose directions generators generators_square,
    operator_translation,mode_operator m hm]

end
end FourierSchur.OriginalProjectionFrameAlphabet
