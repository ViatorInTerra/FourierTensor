import work_in_progress.OriginalProjectionNativeDirections
import work_in_progress.OriginalProjectionNativeGenerators
namespace FourierSchur.OriginalProjectionNativeFrameDictionary
open OAI.PowerSaving OAI.PowerSaving.Binary Matrix Finset
open OriginalBinaryMatrixCertificates OriginalProjectionNativeDirections
open OriginalNativeGeneratorRealization OriginalProjectionNativeGenerators
open OriginalProjectionNativeRowCertificate
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000
def baseRows : Array (OBase (Fin 125)) := #[OBase.canonical (Fin 125),b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,b22,b23,b24,b25,b26,b27,b28,b29,b30,b31,b32,b33,b34,b35,b36,b37,b38,b39,b40,b41,b42,b43,b44,b45,b46,b47,b48,b49,b50,b51,b52,b53,b54,b55,b56,b57,b58,b59,b60,b61,b62,b63]
def nativeBase (i : Fin 65) : OBase (Fin 125) := baseRows.getD i.val (OBase.canonical (Fin 125))
def pivotRows : Array (Fin 125) := #[0,1,1,1,1,1,2,2,2,2,3,3,3,3,1,1,1,3,3,3,1,1,1,1,1,1,3,1,1,1,1,1,1,2,2,2,3,3,1,1,1,1,2,2,2,3,3,1,1,1,1,2,2,2,3,3,1,1,1,1,2,2,2,3,3]
def pivot (i : Fin 65) : Fin 125 := pivotRows.getD i.val 0
theorem basis_direction (i : Fin 65) (hi : i≠0) :
    (nativeBase i).v (pivot i)=wordVector 125 (directions i) := by
  fin_cases i
  · exact False.elim (hi rfl)
  · change b0.v 1=wordVector 125 0xd6b4006b5a0035ad
    exact b0_pivot
  · change b1.v 1=wordVector 125 0x1ad6800d6b40000000035ad
    exact b1_pivot
  · change b2.v 1=wordVector 125 0x35ad001ad680000000000000035ad
    exact b2_pivot
  · change b3.v 1=wordVector 125 0x35ad0000000000000006b5a0035ad
    exact b3_pivot
  · change b4.v 1=wordVector 125 0x6739000000000000000ce72006739
    exact b4_pivot
  · change b5.v 2=wordVector 125 0x4e730027398000000000000004e73
    exact b5_pivot
  · change b6.v 2=wordVector 125 0x273980139cc000000004e73
    exact b6_pivot
  · change b7.v 2=wordVector 125 0x139cc009ce6004e73
    exact b7_pivot
  · change b8.v 2=wordVector 125 0x4e730000000000000009ce6004e73
    exact b8_pivot
  · change b9.v 3=wordVector 125 0x1ce0380e701c000000039c07
    exact b9_pivot
  · change b10.v 3=wordVector 125 0x39c07000000000000007380e039c07
    exact b10_pivot
  · change b11.v 3=wordVector 125 0xe701c07380e039c07
    exact b11_pivot
  · change b12.v 3=wordVector 125 0x39c0701ce038000000000000039c07
    exact b12_pivot
  · change b13.v 1=wordVector 125 0x35a0681ad03400000006b40d
    exact b13_pivot
  · change b14.v 1=wordVector 125 0x6b40d035a06800000000000006b40d
    exact b14_pivot
  · change b15.v 1=wordVector 125 0x6b40d00000000000000d681a06b40d
    exact b15_pivot
  · change b16.v 3=wordVector 125 0x39c0039ce001c000000738007
    exact b16_pivot
  · change b17.v 3=wordVector 125 0x73800739c0038000000000000738007
    exact b17_pivot
  · change b18.v 3=wordVector 125 0x7380070000000000000e7000e738007
    exact b18_pivot
  · change b19.v 1=wordVector 125 0x35a0035ad001ad6800d
    exact b19_pivot
  · change b20.v 1=wordVector 125 0x6b4006b5a0034000000d6800d
    exact b20_pivot
  · change b21.v 1=wordVector 125 0xd6800d6b40068000000000000d6800d
    exact b21_pivot
  · change b22.v 1=wordVector 125 0x6800d6b4006b4000000d001ad
    exact b22_pivot
  · change b23.v 1=wordVector 125 0xd001ad6800d68000000000000d001ad
    exact b23_pivot
  · change b24.v 1=wordVector 125 0xd001ad0000000000001a0035ad001ad
    exact b24_pivot
  · change b25.v 3=wordVector 125 0x739c0039ce001ce7
    exact b25_pivot
  · change b26.v 1=wordVector 125 0x1ad0340d681a06b40d
    exact b26_pivot
  · change b27.v 1=wordVector 125 0x34006b5a0035ad001ad
    exact b27_pivot
  · change b28.v 1=wordVector 125 0x19ce400ce72006739
    exact b28_pivot
  · change b29.v 1=wordVector 125 0x33906419c8320ce419
    exact b29_pivot
  · change b30.v 1=wordVector 125 0x67200673900339c8019
    exact b30_pivot
  · change b31.v 1=wordVector 125 0x6400ce7200673900339
    exact b31_pivot
  · change b32.v 2=wordVector 125 0x27304c13982609cc13
    exact b32_pivot
  · change b33.v 2=wordVector 125 0x4e6004e730027398013
    exact b33_pivot
  · change b34.v 2=wordVector 125 0x4c009ce6004e7300273
    exact b34_pivot
  · change b35.v 3=wordVector 125 0x3800739c0039c0000007000e7
    exact b35_pivot
  · change b36.v 3=wordVector 125 0xe73800739c000000001ce7
    exact b36_pivot
  · change b37.v 1=wordVector 125 0x339c8019ce4000000006739
    exact b37_pivot
  · change b38.v 1=wordVector 125 0x6720c83390640000000ce419
    exact b38_pivot
  · change b39.v 1=wordVector 125 0xce400ce7200640000019c8019
    exact b39_pivot
  · change b40.v 1=wordVector 125 0xc8019ce400ce4000001900339
    exact b40_pivot
  · change b41.v 2=wordVector 125 0x4e609827304c00000009cc13
    exact b41_pivot
  · change b42.v 2=wordVector 125 0x9cc009ce6004c000001398013
    exact b42_pivot
  · change b43.v 2=wordVector 125 0x980139cc009cc000001300273
    exact b43_pivot
  · change b44.v 3=wordVector 125 0x1ce7000e738000000000000001ce7
    exact b44_pivot
  · change b45.v 3=wordVector 125 0x7000e738007380000000000007000e7
    exact b45_pivot
  · change b46.v 1=wordVector 125 0x673900339c8000000000000006739
    exact b46_pivot
  · change b47.v 1=wordVector 125 0xce41906720c80000000000000ce419
    exact b47_pivot
  · change b48.v 1=wordVector 125 0x19c8019ce400c80000000000019c8019
    exact b48_pivot
  · change b49.v 1=wordVector 125 0x1900339c8019c8000000000001900339
    exact b49_pivot
  · change b50.v 2=wordVector 125 0x9cc1304e609800000000000009cc13
    exact b50_pivot
  · change b51.v 2=wordVector 125 0x13980139cc0098000000000001398013
    exact b51_pivot
  · change b52.v 2=wordVector 125 0x13002739801398000000000001300273
    exact b52_pivot
  · change b53.v 3=wordVector 125 0x1ce700000000000000039ce001ce7
    exact b53_pivot
  · change b54.v 3=wordVector 125 0x7000e70000000000000e001ce7000e7
    exact b54_pivot
  · change b55.v 1=wordVector 125 0xd6800d0000000000001ad001ad6800d
    exact b55_pivot
  · change b56.v 1=wordVector 125 0xce419000000000000019c8320ce419
    exact b56_pivot
  · change b57.v 1=wordVector 125 0x19c801900000000000033900339c8019
    exact b57_pivot
  · change b58.v 1=wordVector 125 0x19003390000000000003200673900339
    exact b58_pivot
  · change b59.v 2=wordVector 125 0x9cc13000000000000013982609cc13
    exact b59_pivot
  · change b60.v 2=wordVector 125 0x13980130000000000002730027398013
    exact b60_pivot
  · change b61.v 2=wordVector 125 0x130027300000000000026004e7300273
    exact b61_pivot
  · change b62.v 3=wordVector 125 0x1c0039ce001ce7000e7
    exact b62_pivot
  · change b63.v 3=wordVector 125 0x1ce001ce7000e738007
    exact b63_pivot
theorem frame_line (i : Fin 65) (hi : i≠0) :
    frame (nativeBase i) {pivot i}=OriginalNativeGeneratorSymbols.operator generators ⟨2^i.val,0⟩ := by
  rw [singleton_frame,basis_direction i hi]
  exact (line_operator i hi).symm
end
end FourierSchur.OriginalProjectionNativeFrameDictionary
