import work_in_progress.OriginalJointNativeDirections
import work_in_progress.OriginalJointNativeGenerators
namespace FourierSchur.OriginalJointNativeFrameDictionary
open OAI.PowerSaving OAI.PowerSaving.Binary Matrix Finset
open OriginalBinaryMatrixCertificates OriginalJointNativeDirections
open OriginalNativeGeneratorRealization OriginalJointNativeGenerators
open OriginalJointNativeRowCertificate
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000
def baseRows : Array (OBase (Fin 216)) := #[OBase.canonical (Fin 216),b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,b22,b23,b24,b25,b26,b27,b28,b29,b30,b31,b32,b33,b34,b35,b36,b37,b38,b39,b40,b41,b42,b43,b44,b45]
def nativeBase (i : Fin 47) : OBase (Fin 216) := baseRows.getD i.val (OBase.canonical (Fin 216))
def pivotRows : Array (Fin 216) := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def pivot (i : Fin 47) : Fin 216 := pivotRows.getD i.val 0
theorem basis_direction (i : Fin 47) (hi : i≠0) :
    (nativeBase i).v (pivot i)=wordVector 216 (directions i) := by
  fin_cases i
  · exact False.elim (hi rfl)
  · change b0.v 0=wordVector 216 0x71c01c00000000000071c01c00071c01c000000000000000000000
    exact b0_pivot
  · change b1.v 0=wordVector 216 0x71c01c00071c01c00000000000071c01c000000000000000000000
    exact b1_pivot
  · change b2.v 0=wordVector 216 0x71c01c00071c01c00071c01c000000000000000000000000000000
    exact b2_pivot
  · change b3.v 0=wordVector 216 0xb2c02c000b2c02c000b2c02c000000000000000000000
    exact b3_pivot
  · change b4.v 0=wordVector 216 0xb2c02c000000000000b2c02c000b2c02c000000000000000000000
    exact b4_pivot
  · change b5.v 0=wordVector 216 0xb2c02c000b2c02c000000000000b2c02c000000000000000000000
    exact b5_pivot
  · change b6.v 0=wordVector 216 0xb2c02c000b2c02c000b2c02c000000000000000000000000000000
    exact b6_pivot
  · change b7.v 0=wordVector 216 0x34d34000034d34000034d34000000000000000000000
    exact b7_pivot
  · change b8.v 0=wordVector 216 0x38e38000038e38000038e38000000000000000000000
    exact b8_pivot
  · change b9.v 0=wordVector 216 0xd00d34000d00d34000d00d34000000000000000000000
    exact b9_pivot
  · change b10.v 0=wordVector 216 0xd34034000d34034000d34034000000000000000000000
    exact b10_pivot
  · change b11.v 0=wordVector 216 0xd34d00000d34d00000d34d00000000000000000000000
    exact b11_pivot
  · change b12.v 0=wordVector 216 0xe38e00000e38e00000e38e00000000000000000000000
    exact b12_pivot
  · change b13.v 0=wordVector 216 0x1c71c00000000000001c71c00001c71c000000000000000000000
    exact b13_pivot
  · change b14.v 0=wordVector 216 0x34d34000000000000034d34000034d34000000000000000000000
    exact b14_pivot
  · change b15.v 0=wordVector 216 0x38e38000000000000038e38000038e38000000000000000000000
    exact b15_pivot
  · change b16.v 0=wordVector 216 0xd00d34000000000000d00d34000d00d34000000000000000000000
    exact b16_pivot
  · change b17.v 0=wordVector 216 0xe00e38000000000000e00e38000e00e38000000000000000000000
    exact b17_pivot
  · change b18.v 0=wordVector 216 0xd34034000000000000d34034000d34034000000000000000000000
    exact b18_pivot
  · change b19.v 0=wordVector 216 0xe38038000000000000e38038000e38038000000000000000000000
    exact b19_pivot
  · change b20.v 0=wordVector 216 0x71c70000000000000071c70000071c700000000000000000000000
    exact b20_pivot
  · change b21.v 0=wordVector 216 0xb2cb00000000000000b2cb00000b2cb00000000000000000000000
    exact b21_pivot
  · change b22.v 0=wordVector 216 0xd34d00000000000000d34d00000d34d00000000000000000000000
    exact b22_pivot
  · change b23.v 0=wordVector 216 0xe38e00000000000000e38e00000e38e00000000000000000000000
    exact b23_pivot
  · change b24.v 0=wordVector 216 0x1c71c00001c71c00000000000001c71c000000000000000000000
    exact b24_pivot
  · change b25.v 0=wordVector 216 0x34d34000034d34000000000000034d34000000000000000000000
    exact b25_pivot
  · change b26.v 0=wordVector 216 0xd00d34000d00d34000000000000d00d34000000000000000000000
    exact b26_pivot
  · change b27.v 0=wordVector 216 0xe00e38000e00e38000000000000e00e38000000000000000000000
    exact b27_pivot
  · change b28.v 0=wordVector 216 0xd34034000d34034000000000000d34034000000000000000000000
    exact b28_pivot
  · change b29.v 0=wordVector 216 0xe38038000e38038000000000000e38038000000000000000000000
    exact b29_pivot
  · change b30.v 0=wordVector 216 0x71c70000071c70000000000000071c700000000000000000000000
    exact b30_pivot
  · change b31.v 0=wordVector 216 0xb2cb00000b2cb00000000000000b2cb00000000000000000000000
    exact b31_pivot
  · change b32.v 0=wordVector 216 0xd34d00000d34d00000000000000d34d00000000000000000000000
    exact b32_pivot
  · change b33.v 0=wordVector 216 0xe38e00000e38e00000000000000e38e00000000000000000000000
    exact b33_pivot
  · change b34.v 0=wordVector 216 0x1c71c00001c71c00001c71c000000000000000000000000000000
    exact b34_pivot
  · change b35.v 0=wordVector 216 0x34d34000034d34000034d34000000000000000000000000000000
    exact b35_pivot
  · change b36.v 0=wordVector 216 0xd00d34000d00d34000d00d34000000000000000000000000000000
    exact b36_pivot
  · change b37.v 0=wordVector 216 0xe00e38000e00e38000e00e38000000000000000000000000000000
    exact b37_pivot
  · change b38.v 0=wordVector 216 0xd34034000d34034000d34034000000000000000000000000000000
    exact b38_pivot
  · change b39.v 0=wordVector 216 0xe38038000e38038000e38038000000000000000000000000000000
    exact b39_pivot
  · change b40.v 0=wordVector 216 0x71c70000071c70000071c700000000000000000000000000000000
    exact b40_pivot
  · change b41.v 0=wordVector 216 0xb2cb00000b2cb00000b2cb00000000000000000000000000000000
    exact b41_pivot
  · change b42.v 0=wordVector 216 0xd34d00000d34d00000d34d00000000000000000000000000000000
    exact b42_pivot
  · change b43.v 0=wordVector 216 0xe38e00000e38e00000e38e00000000000000000000000000000000
    exact b43_pivot
  · change b44.v 0=wordVector 216 0xb2cb00000b2cb00000b2cb00000000000000000000000
    exact b44_pivot
  · change b45.v 0=wordVector 216 0x1c71c00001c71c00001c71c000000000000000000000
    exact b45_pivot
theorem frame_line (i : Fin 47) (hi : i≠0) :
    frame (nativeBase i) {pivot i}=OriginalNativeGeneratorSymbols.operator generators ⟨2^i.val,0⟩ := by
  rw [singleton_frame,basis_direction i hi]
  exact (line_operator i hi).symm
end
end FourierSchur.OriginalJointNativeFrameDictionary
