import work_in_progress.OriginalCheckedNativeDirection
namespace FourierSchur.OriginalProjectionNativeDirections
open OAI.PowerSaving OAI.PowerSaving.Binary Matrix Finset
open OriginalBinaryMatrixCertificates OriginalCheckedNativeDirection
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000
def v0 : Space (Fin 125) := wordVector 125 0xd6b4006b5a0035ad
theorem v0_self_check : fastDot 125 0xd6b4006b5a0035ad 0xd6b4006b5a0035ad=1 := by decide
theorem v0_zero_check : bitValue 0xd6b4006b5a0035ad 1=0 := by decide
def b0 : OBase (Fin 125) := basis 125 0xd6b4006b5a0035ad 1 v0_self_check v0_zero_check
theorem b0_pivot : b0.v 1=v0 := basis_pivot 125 0xd6b4006b5a0035ad 1 _ _
def v1 : Space (Fin 125) := wordVector 125 0x1ad6800d6b40000000035ad
theorem v1_self_check : fastDot 125 0x1ad6800d6b40000000035ad 0x1ad6800d6b40000000035ad=1 := by decide
theorem v1_zero_check : bitValue 0x1ad6800d6b40000000035ad 1=0 := by decide
def b1 : OBase (Fin 125) := basis 125 0x1ad6800d6b40000000035ad 1 v1_self_check v1_zero_check
theorem b1_pivot : b1.v 1=v1 := basis_pivot 125 0x1ad6800d6b40000000035ad 1 _ _
def v2 : Space (Fin 125) := wordVector 125 0x35ad001ad680000000000000035ad
theorem v2_self_check : fastDot 125 0x35ad001ad680000000000000035ad 0x35ad001ad680000000000000035ad=1 := by decide
theorem v2_zero_check : bitValue 0x35ad001ad680000000000000035ad 1=0 := by decide
def b2 : OBase (Fin 125) := basis 125 0x35ad001ad680000000000000035ad 1 v2_self_check v2_zero_check
theorem b2_pivot : b2.v 1=v2 := basis_pivot 125 0x35ad001ad680000000000000035ad 1 _ _
def v3 : Space (Fin 125) := wordVector 125 0x35ad0000000000000006b5a0035ad
theorem v3_self_check : fastDot 125 0x35ad0000000000000006b5a0035ad 0x35ad0000000000000006b5a0035ad=1 := by decide
theorem v3_zero_check : bitValue 0x35ad0000000000000006b5a0035ad 1=0 := by decide
def b3 : OBase (Fin 125) := basis 125 0x35ad0000000000000006b5a0035ad 1 v3_self_check v3_zero_check
theorem b3_pivot : b3.v 1=v3 := basis_pivot 125 0x35ad0000000000000006b5a0035ad 1 _ _
def v4 : Space (Fin 125) := wordVector 125 0x6739000000000000000ce72006739
theorem v4_self_check : fastDot 125 0x6739000000000000000ce72006739 0x6739000000000000000ce72006739=1 := by decide
theorem v4_zero_check : bitValue 0x6739000000000000000ce72006739 1=0 := by decide
def b4 : OBase (Fin 125) := basis 125 0x6739000000000000000ce72006739 1 v4_self_check v4_zero_check
theorem b4_pivot : b4.v 1=v4 := basis_pivot 125 0x6739000000000000000ce72006739 1 _ _
def v5 : Space (Fin 125) := wordVector 125 0x4e730027398000000000000004e73
theorem v5_self_check : fastDot 125 0x4e730027398000000000000004e73 0x4e730027398000000000000004e73=1 := by decide
theorem v5_zero_check : bitValue 0x4e730027398000000000000004e73 2=0 := by decide
def b5 : OBase (Fin 125) := basis 125 0x4e730027398000000000000004e73 2 v5_self_check v5_zero_check
theorem b5_pivot : b5.v 2=v5 := basis_pivot 125 0x4e730027398000000000000004e73 2 _ _
def v6 : Space (Fin 125) := wordVector 125 0x273980139cc000000004e73
theorem v6_self_check : fastDot 125 0x273980139cc000000004e73 0x273980139cc000000004e73=1 := by decide
theorem v6_zero_check : bitValue 0x273980139cc000000004e73 2=0 := by decide
def b6 : OBase (Fin 125) := basis 125 0x273980139cc000000004e73 2 v6_self_check v6_zero_check
theorem b6_pivot : b6.v 2=v6 := basis_pivot 125 0x273980139cc000000004e73 2 _ _
def v7 : Space (Fin 125) := wordVector 125 0x139cc009ce6004e73
theorem v7_self_check : fastDot 125 0x139cc009ce6004e73 0x139cc009ce6004e73=1 := by decide
theorem v7_zero_check : bitValue 0x139cc009ce6004e73 2=0 := by decide
def b7 : OBase (Fin 125) := basis 125 0x139cc009ce6004e73 2 v7_self_check v7_zero_check
theorem b7_pivot : b7.v 2=v7 := basis_pivot 125 0x139cc009ce6004e73 2 _ _
def v8 : Space (Fin 125) := wordVector 125 0x4e730000000000000009ce6004e73
theorem v8_self_check : fastDot 125 0x4e730000000000000009ce6004e73 0x4e730000000000000009ce6004e73=1 := by decide
theorem v8_zero_check : bitValue 0x4e730000000000000009ce6004e73 2=0 := by decide
def b8 : OBase (Fin 125) := basis 125 0x4e730000000000000009ce6004e73 2 v8_self_check v8_zero_check
theorem b8_pivot : b8.v 2=v8 := basis_pivot 125 0x4e730000000000000009ce6004e73 2 _ _
def v9 : Space (Fin 125) := wordVector 125 0x1ce0380e701c000000039c07
theorem v9_self_check : fastDot 125 0x1ce0380e701c000000039c07 0x1ce0380e701c000000039c07=1 := by decide
theorem v9_zero_check : bitValue 0x1ce0380e701c000000039c07 3=0 := by decide
def b9 : OBase (Fin 125) := basis 125 0x1ce0380e701c000000039c07 3 v9_self_check v9_zero_check
theorem b9_pivot : b9.v 3=v9 := basis_pivot 125 0x1ce0380e701c000000039c07 3 _ _
def v10 : Space (Fin 125) := wordVector 125 0x39c07000000000000007380e039c07
theorem v10_self_check : fastDot 125 0x39c07000000000000007380e039c07 0x39c07000000000000007380e039c07=1 := by decide
theorem v10_zero_check : bitValue 0x39c07000000000000007380e039c07 3=0 := by decide
def b10 : OBase (Fin 125) := basis 125 0x39c07000000000000007380e039c07 3 v10_self_check v10_zero_check
theorem b10_pivot : b10.v 3=v10 := basis_pivot 125 0x39c07000000000000007380e039c07 3 _ _
def v11 : Space (Fin 125) := wordVector 125 0xe701c07380e039c07
theorem v11_self_check : fastDot 125 0xe701c07380e039c07 0xe701c07380e039c07=1 := by decide
theorem v11_zero_check : bitValue 0xe701c07380e039c07 3=0 := by decide
def b11 : OBase (Fin 125) := basis 125 0xe701c07380e039c07 3 v11_self_check v11_zero_check
theorem b11_pivot : b11.v 3=v11 := basis_pivot 125 0xe701c07380e039c07 3 _ _
def v12 : Space (Fin 125) := wordVector 125 0x39c0701ce038000000000000039c07
theorem v12_self_check : fastDot 125 0x39c0701ce038000000000000039c07 0x39c0701ce038000000000000039c07=1 := by decide
theorem v12_zero_check : bitValue 0x39c0701ce038000000000000039c07 3=0 := by decide
def b12 : OBase (Fin 125) := basis 125 0x39c0701ce038000000000000039c07 3 v12_self_check v12_zero_check
theorem b12_pivot : b12.v 3=v12 := basis_pivot 125 0x39c0701ce038000000000000039c07 3 _ _
def v13 : Space (Fin 125) := wordVector 125 0x35a0681ad03400000006b40d
theorem v13_self_check : fastDot 125 0x35a0681ad03400000006b40d 0x35a0681ad03400000006b40d=1 := by decide
theorem v13_zero_check : bitValue 0x35a0681ad03400000006b40d 1=0 := by decide
def b13 : OBase (Fin 125) := basis 125 0x35a0681ad03400000006b40d 1 v13_self_check v13_zero_check
theorem b13_pivot : b13.v 1=v13 := basis_pivot 125 0x35a0681ad03400000006b40d 1 _ _
def v14 : Space (Fin 125) := wordVector 125 0x6b40d035a06800000000000006b40d
theorem v14_self_check : fastDot 125 0x6b40d035a06800000000000006b40d 0x6b40d035a06800000000000006b40d=1 := by decide
theorem v14_zero_check : bitValue 0x6b40d035a06800000000000006b40d 1=0 := by decide
def b14 : OBase (Fin 125) := basis 125 0x6b40d035a06800000000000006b40d 1 v14_self_check v14_zero_check
theorem b14_pivot : b14.v 1=v14 := basis_pivot 125 0x6b40d035a06800000000000006b40d 1 _ _
def v15 : Space (Fin 125) := wordVector 125 0x6b40d00000000000000d681a06b40d
theorem v15_self_check : fastDot 125 0x6b40d00000000000000d681a06b40d 0x6b40d00000000000000d681a06b40d=1 := by decide
theorem v15_zero_check : bitValue 0x6b40d00000000000000d681a06b40d 1=0 := by decide
def b15 : OBase (Fin 125) := basis 125 0x6b40d00000000000000d681a06b40d 1 v15_self_check v15_zero_check
theorem b15_pivot : b15.v 1=v15 := basis_pivot 125 0x6b40d00000000000000d681a06b40d 1 _ _
def v16 : Space (Fin 125) := wordVector 125 0x39c0039ce001c000000738007
theorem v16_self_check : fastDot 125 0x39c0039ce001c000000738007 0x39c0039ce001c000000738007=1 := by decide
theorem v16_zero_check : bitValue 0x39c0039ce001c000000738007 3=0 := by decide
def b16 : OBase (Fin 125) := basis 125 0x39c0039ce001c000000738007 3 v16_self_check v16_zero_check
theorem b16_pivot : b16.v 3=v16 := basis_pivot 125 0x39c0039ce001c000000738007 3 _ _
def v17 : Space (Fin 125) := wordVector 125 0x73800739c0038000000000000738007
theorem v17_self_check : fastDot 125 0x73800739c0038000000000000738007 0x73800739c0038000000000000738007=1 := by decide
theorem v17_zero_check : bitValue 0x73800739c0038000000000000738007 3=0 := by decide
def b17 : OBase (Fin 125) := basis 125 0x73800739c0038000000000000738007 3 v17_self_check v17_zero_check
theorem b17_pivot : b17.v 3=v17 := basis_pivot 125 0x73800739c0038000000000000738007 3 _ _
def v18 : Space (Fin 125) := wordVector 125 0x7380070000000000000e7000e738007
theorem v18_self_check : fastDot 125 0x7380070000000000000e7000e738007 0x7380070000000000000e7000e738007=1 := by decide
theorem v18_zero_check : bitValue 0x7380070000000000000e7000e738007 3=0 := by decide
def b18 : OBase (Fin 125) := basis 125 0x7380070000000000000e7000e738007 3 v18_self_check v18_zero_check
theorem b18_pivot : b18.v 3=v18 := basis_pivot 125 0x7380070000000000000e7000e738007 3 _ _
def v19 : Space (Fin 125) := wordVector 125 0x35a0035ad001ad6800d
theorem v19_self_check : fastDot 125 0x35a0035ad001ad6800d 0x35a0035ad001ad6800d=1 := by decide
theorem v19_zero_check : bitValue 0x35a0035ad001ad6800d 1=0 := by decide
def b19 : OBase (Fin 125) := basis 125 0x35a0035ad001ad6800d 1 v19_self_check v19_zero_check
theorem b19_pivot : b19.v 1=v19 := basis_pivot 125 0x35a0035ad001ad6800d 1 _ _
def v20 : Space (Fin 125) := wordVector 125 0x6b4006b5a0034000000d6800d
theorem v20_self_check : fastDot 125 0x6b4006b5a0034000000d6800d 0x6b4006b5a0034000000d6800d=1 := by decide
theorem v20_zero_check : bitValue 0x6b4006b5a0034000000d6800d 1=0 := by decide
def b20 : OBase (Fin 125) := basis 125 0x6b4006b5a0034000000d6800d 1 v20_self_check v20_zero_check
theorem b20_pivot : b20.v 1=v20 := basis_pivot 125 0x6b4006b5a0034000000d6800d 1 _ _
def v21 : Space (Fin 125) := wordVector 125 0xd6800d6b40068000000000000d6800d
theorem v21_self_check : fastDot 125 0xd6800d6b40068000000000000d6800d 0xd6800d6b40068000000000000d6800d=1 := by decide
theorem v21_zero_check : bitValue 0xd6800d6b40068000000000000d6800d 1=0 := by decide
def b21 : OBase (Fin 125) := basis 125 0xd6800d6b40068000000000000d6800d 1 v21_self_check v21_zero_check
theorem b21_pivot : b21.v 1=v21 := basis_pivot 125 0xd6800d6b40068000000000000d6800d 1 _ _
def v22 : Space (Fin 125) := wordVector 125 0x6800d6b4006b4000000d001ad
theorem v22_self_check : fastDot 125 0x6800d6b4006b4000000d001ad 0x6800d6b4006b4000000d001ad=1 := by decide
theorem v22_zero_check : bitValue 0x6800d6b4006b4000000d001ad 1=0 := by decide
def b22 : OBase (Fin 125) := basis 125 0x6800d6b4006b4000000d001ad 1 v22_self_check v22_zero_check
theorem b22_pivot : b22.v 1=v22 := basis_pivot 125 0x6800d6b4006b4000000d001ad 1 _ _
def v23 : Space (Fin 125) := wordVector 125 0xd001ad6800d68000000000000d001ad
theorem v23_self_check : fastDot 125 0xd001ad6800d68000000000000d001ad 0xd001ad6800d68000000000000d001ad=1 := by decide
theorem v23_zero_check : bitValue 0xd001ad6800d68000000000000d001ad 1=0 := by decide
def b23 : OBase (Fin 125) := basis 125 0xd001ad6800d68000000000000d001ad 1 v23_self_check v23_zero_check
theorem b23_pivot : b23.v 1=v23 := basis_pivot 125 0xd001ad6800d68000000000000d001ad 1 _ _
def v24 : Space (Fin 125) := wordVector 125 0xd001ad0000000000001a0035ad001ad
theorem v24_self_check : fastDot 125 0xd001ad0000000000001a0035ad001ad 0xd001ad0000000000001a0035ad001ad=1 := by decide
theorem v24_zero_check : bitValue 0xd001ad0000000000001a0035ad001ad 1=0 := by decide
def b24 : OBase (Fin 125) := basis 125 0xd001ad0000000000001a0035ad001ad 1 v24_self_check v24_zero_check
theorem b24_pivot : b24.v 1=v24 := basis_pivot 125 0xd001ad0000000000001a0035ad001ad 1 _ _
def v25 : Space (Fin 125) := wordVector 125 0x739c0039ce001ce7
theorem v25_self_check : fastDot 125 0x739c0039ce001ce7 0x739c0039ce001ce7=1 := by decide
theorem v25_zero_check : bitValue 0x739c0039ce001ce7 3=0 := by decide
def b25 : OBase (Fin 125) := basis 125 0x739c0039ce001ce7 3 v25_self_check v25_zero_check
theorem b25_pivot : b25.v 3=v25 := basis_pivot 125 0x739c0039ce001ce7 3 _ _
def v26 : Space (Fin 125) := wordVector 125 0x1ad0340d681a06b40d
theorem v26_self_check : fastDot 125 0x1ad0340d681a06b40d 0x1ad0340d681a06b40d=1 := by decide
theorem v26_zero_check : bitValue 0x1ad0340d681a06b40d 1=0 := by decide
def b26 : OBase (Fin 125) := basis 125 0x1ad0340d681a06b40d 1 v26_self_check v26_zero_check
theorem b26_pivot : b26.v 1=v26 := basis_pivot 125 0x1ad0340d681a06b40d 1 _ _
def v27 : Space (Fin 125) := wordVector 125 0x34006b5a0035ad001ad
theorem v27_self_check : fastDot 125 0x34006b5a0035ad001ad 0x34006b5a0035ad001ad=1 := by decide
theorem v27_zero_check : bitValue 0x34006b5a0035ad001ad 1=0 := by decide
def b27 : OBase (Fin 125) := basis 125 0x34006b5a0035ad001ad 1 v27_self_check v27_zero_check
theorem b27_pivot : b27.v 1=v27 := basis_pivot 125 0x34006b5a0035ad001ad 1 _ _
def v28 : Space (Fin 125) := wordVector 125 0x19ce400ce72006739
theorem v28_self_check : fastDot 125 0x19ce400ce72006739 0x19ce400ce72006739=1 := by decide
theorem v28_zero_check : bitValue 0x19ce400ce72006739 1=0 := by decide
def b28 : OBase (Fin 125) := basis 125 0x19ce400ce72006739 1 v28_self_check v28_zero_check
theorem b28_pivot : b28.v 1=v28 := basis_pivot 125 0x19ce400ce72006739 1 _ _
def v29 : Space (Fin 125) := wordVector 125 0x33906419c8320ce419
theorem v29_self_check : fastDot 125 0x33906419c8320ce419 0x33906419c8320ce419=1 := by decide
theorem v29_zero_check : bitValue 0x33906419c8320ce419 1=0 := by decide
def b29 : OBase (Fin 125) := basis 125 0x33906419c8320ce419 1 v29_self_check v29_zero_check
theorem b29_pivot : b29.v 1=v29 := basis_pivot 125 0x33906419c8320ce419 1 _ _
def v30 : Space (Fin 125) := wordVector 125 0x67200673900339c8019
theorem v30_self_check : fastDot 125 0x67200673900339c8019 0x67200673900339c8019=1 := by decide
theorem v30_zero_check : bitValue 0x67200673900339c8019 1=0 := by decide
def b30 : OBase (Fin 125) := basis 125 0x67200673900339c8019 1 v30_self_check v30_zero_check
theorem b30_pivot : b30.v 1=v30 := basis_pivot 125 0x67200673900339c8019 1 _ _
def v31 : Space (Fin 125) := wordVector 125 0x6400ce7200673900339
theorem v31_self_check : fastDot 125 0x6400ce7200673900339 0x6400ce7200673900339=1 := by decide
theorem v31_zero_check : bitValue 0x6400ce7200673900339 1=0 := by decide
def b31 : OBase (Fin 125) := basis 125 0x6400ce7200673900339 1 v31_self_check v31_zero_check
theorem b31_pivot : b31.v 1=v31 := basis_pivot 125 0x6400ce7200673900339 1 _ _
def v32 : Space (Fin 125) := wordVector 125 0x27304c13982609cc13
theorem v32_self_check : fastDot 125 0x27304c13982609cc13 0x27304c13982609cc13=1 := by decide
theorem v32_zero_check : bitValue 0x27304c13982609cc13 2=0 := by decide
def b32 : OBase (Fin 125) := basis 125 0x27304c13982609cc13 2 v32_self_check v32_zero_check
theorem b32_pivot : b32.v 2=v32 := basis_pivot 125 0x27304c13982609cc13 2 _ _
def v33 : Space (Fin 125) := wordVector 125 0x4e6004e730027398013
theorem v33_self_check : fastDot 125 0x4e6004e730027398013 0x4e6004e730027398013=1 := by decide
theorem v33_zero_check : bitValue 0x4e6004e730027398013 2=0 := by decide
def b33 : OBase (Fin 125) := basis 125 0x4e6004e730027398013 2 v33_self_check v33_zero_check
theorem b33_pivot : b33.v 2=v33 := basis_pivot 125 0x4e6004e730027398013 2 _ _
def v34 : Space (Fin 125) := wordVector 125 0x4c009ce6004e7300273
theorem v34_self_check : fastDot 125 0x4c009ce6004e7300273 0x4c009ce6004e7300273=1 := by decide
theorem v34_zero_check : bitValue 0x4c009ce6004e7300273 2=0 := by decide
def b34 : OBase (Fin 125) := basis 125 0x4c009ce6004e7300273 2 v34_self_check v34_zero_check
theorem b34_pivot : b34.v 2=v34 := basis_pivot 125 0x4c009ce6004e7300273 2 _ _
def v35 : Space (Fin 125) := wordVector 125 0x3800739c0039c0000007000e7
theorem v35_self_check : fastDot 125 0x3800739c0039c0000007000e7 0x3800739c0039c0000007000e7=1 := by decide
theorem v35_zero_check : bitValue 0x3800739c0039c0000007000e7 3=0 := by decide
def b35 : OBase (Fin 125) := basis 125 0x3800739c0039c0000007000e7 3 v35_self_check v35_zero_check
theorem b35_pivot : b35.v 3=v35 := basis_pivot 125 0x3800739c0039c0000007000e7 3 _ _
def v36 : Space (Fin 125) := wordVector 125 0xe73800739c000000001ce7
theorem v36_self_check : fastDot 125 0xe73800739c000000001ce7 0xe73800739c000000001ce7=1 := by decide
theorem v36_zero_check : bitValue 0xe73800739c000000001ce7 3=0 := by decide
def b36 : OBase (Fin 125) := basis 125 0xe73800739c000000001ce7 3 v36_self_check v36_zero_check
theorem b36_pivot : b36.v 3=v36 := basis_pivot 125 0xe73800739c000000001ce7 3 _ _
def v37 : Space (Fin 125) := wordVector 125 0x339c8019ce4000000006739
theorem v37_self_check : fastDot 125 0x339c8019ce4000000006739 0x339c8019ce4000000006739=1 := by decide
theorem v37_zero_check : bitValue 0x339c8019ce4000000006739 1=0 := by decide
def b37 : OBase (Fin 125) := basis 125 0x339c8019ce4000000006739 1 v37_self_check v37_zero_check
theorem b37_pivot : b37.v 1=v37 := basis_pivot 125 0x339c8019ce4000000006739 1 _ _
def v38 : Space (Fin 125) := wordVector 125 0x6720c83390640000000ce419
theorem v38_self_check : fastDot 125 0x6720c83390640000000ce419 0x6720c83390640000000ce419=1 := by decide
theorem v38_zero_check : bitValue 0x6720c83390640000000ce419 1=0 := by decide
def b38 : OBase (Fin 125) := basis 125 0x6720c83390640000000ce419 1 v38_self_check v38_zero_check
theorem b38_pivot : b38.v 1=v38 := basis_pivot 125 0x6720c83390640000000ce419 1 _ _
def v39 : Space (Fin 125) := wordVector 125 0xce400ce7200640000019c8019
theorem v39_self_check : fastDot 125 0xce400ce7200640000019c8019 0xce400ce7200640000019c8019=1 := by decide
theorem v39_zero_check : bitValue 0xce400ce7200640000019c8019 1=0 := by decide
def b39 : OBase (Fin 125) := basis 125 0xce400ce7200640000019c8019 1 v39_self_check v39_zero_check
theorem b39_pivot : b39.v 1=v39 := basis_pivot 125 0xce400ce7200640000019c8019 1 _ _
def v40 : Space (Fin 125) := wordVector 125 0xc8019ce400ce4000001900339
theorem v40_self_check : fastDot 125 0xc8019ce400ce4000001900339 0xc8019ce400ce4000001900339=1 := by decide
theorem v40_zero_check : bitValue 0xc8019ce400ce4000001900339 1=0 := by decide
def b40 : OBase (Fin 125) := basis 125 0xc8019ce400ce4000001900339 1 v40_self_check v40_zero_check
theorem b40_pivot : b40.v 1=v40 := basis_pivot 125 0xc8019ce400ce4000001900339 1 _ _
def v41 : Space (Fin 125) := wordVector 125 0x4e609827304c00000009cc13
theorem v41_self_check : fastDot 125 0x4e609827304c00000009cc13 0x4e609827304c00000009cc13=1 := by decide
theorem v41_zero_check : bitValue 0x4e609827304c00000009cc13 2=0 := by decide
def b41 : OBase (Fin 125) := basis 125 0x4e609827304c00000009cc13 2 v41_self_check v41_zero_check
theorem b41_pivot : b41.v 2=v41 := basis_pivot 125 0x4e609827304c00000009cc13 2 _ _
def v42 : Space (Fin 125) := wordVector 125 0x9cc009ce6004c000001398013
theorem v42_self_check : fastDot 125 0x9cc009ce6004c000001398013 0x9cc009ce6004c000001398013=1 := by decide
theorem v42_zero_check : bitValue 0x9cc009ce6004c000001398013 2=0 := by decide
def b42 : OBase (Fin 125) := basis 125 0x9cc009ce6004c000001398013 2 v42_self_check v42_zero_check
theorem b42_pivot : b42.v 2=v42 := basis_pivot 125 0x9cc009ce6004c000001398013 2 _ _
def v43 : Space (Fin 125) := wordVector 125 0x980139cc009cc000001300273
theorem v43_self_check : fastDot 125 0x980139cc009cc000001300273 0x980139cc009cc000001300273=1 := by decide
theorem v43_zero_check : bitValue 0x980139cc009cc000001300273 2=0 := by decide
def b43 : OBase (Fin 125) := basis 125 0x980139cc009cc000001300273 2 v43_self_check v43_zero_check
theorem b43_pivot : b43.v 2=v43 := basis_pivot 125 0x980139cc009cc000001300273 2 _ _
def v44 : Space (Fin 125) := wordVector 125 0x1ce7000e738000000000000001ce7
theorem v44_self_check : fastDot 125 0x1ce7000e738000000000000001ce7 0x1ce7000e738000000000000001ce7=1 := by decide
theorem v44_zero_check : bitValue 0x1ce7000e738000000000000001ce7 3=0 := by decide
def b44 : OBase (Fin 125) := basis 125 0x1ce7000e738000000000000001ce7 3 v44_self_check v44_zero_check
theorem b44_pivot : b44.v 3=v44 := basis_pivot 125 0x1ce7000e738000000000000001ce7 3 _ _
def v45 : Space (Fin 125) := wordVector 125 0x7000e738007380000000000007000e7
theorem v45_self_check : fastDot 125 0x7000e738007380000000000007000e7 0x7000e738007380000000000007000e7=1 := by decide
theorem v45_zero_check : bitValue 0x7000e738007380000000000007000e7 3=0 := by decide
def b45 : OBase (Fin 125) := basis 125 0x7000e738007380000000000007000e7 3 v45_self_check v45_zero_check
theorem b45_pivot : b45.v 3=v45 := basis_pivot 125 0x7000e738007380000000000007000e7 3 _ _
def v46 : Space (Fin 125) := wordVector 125 0x673900339c8000000000000006739
theorem v46_self_check : fastDot 125 0x673900339c8000000000000006739 0x673900339c8000000000000006739=1 := by decide
theorem v46_zero_check : bitValue 0x673900339c8000000000000006739 1=0 := by decide
def b46 : OBase (Fin 125) := basis 125 0x673900339c8000000000000006739 1 v46_self_check v46_zero_check
theorem b46_pivot : b46.v 1=v46 := basis_pivot 125 0x673900339c8000000000000006739 1 _ _
def v47 : Space (Fin 125) := wordVector 125 0xce41906720c80000000000000ce419
theorem v47_self_check : fastDot 125 0xce41906720c80000000000000ce419 0xce41906720c80000000000000ce419=1 := by decide
theorem v47_zero_check : bitValue 0xce41906720c80000000000000ce419 1=0 := by decide
def b47 : OBase (Fin 125) := basis 125 0xce41906720c80000000000000ce419 1 v47_self_check v47_zero_check
theorem b47_pivot : b47.v 1=v47 := basis_pivot 125 0xce41906720c80000000000000ce419 1 _ _
def v48 : Space (Fin 125) := wordVector 125 0x19c8019ce400c80000000000019c8019
theorem v48_self_check : fastDot 125 0x19c8019ce400c80000000000019c8019 0x19c8019ce400c80000000000019c8019=1 := by decide
theorem v48_zero_check : bitValue 0x19c8019ce400c80000000000019c8019 1=0 := by decide
def b48 : OBase (Fin 125) := basis 125 0x19c8019ce400c80000000000019c8019 1 v48_self_check v48_zero_check
theorem b48_pivot : b48.v 1=v48 := basis_pivot 125 0x19c8019ce400c80000000000019c8019 1 _ _
def v49 : Space (Fin 125) := wordVector 125 0x1900339c8019c8000000000001900339
theorem v49_self_check : fastDot 125 0x1900339c8019c8000000000001900339 0x1900339c8019c8000000000001900339=1 := by decide
theorem v49_zero_check : bitValue 0x1900339c8019c8000000000001900339 1=0 := by decide
def b49 : OBase (Fin 125) := basis 125 0x1900339c8019c8000000000001900339 1 v49_self_check v49_zero_check
theorem b49_pivot : b49.v 1=v49 := basis_pivot 125 0x1900339c8019c8000000000001900339 1 _ _
def v50 : Space (Fin 125) := wordVector 125 0x9cc1304e609800000000000009cc13
theorem v50_self_check : fastDot 125 0x9cc1304e609800000000000009cc13 0x9cc1304e609800000000000009cc13=1 := by decide
theorem v50_zero_check : bitValue 0x9cc1304e609800000000000009cc13 2=0 := by decide
def b50 : OBase (Fin 125) := basis 125 0x9cc1304e609800000000000009cc13 2 v50_self_check v50_zero_check
theorem b50_pivot : b50.v 2=v50 := basis_pivot 125 0x9cc1304e609800000000000009cc13 2 _ _
def v51 : Space (Fin 125) := wordVector 125 0x13980139cc0098000000000001398013
theorem v51_self_check : fastDot 125 0x13980139cc0098000000000001398013 0x13980139cc0098000000000001398013=1 := by decide
theorem v51_zero_check : bitValue 0x13980139cc0098000000000001398013 2=0 := by decide
def b51 : OBase (Fin 125) := basis 125 0x13980139cc0098000000000001398013 2 v51_self_check v51_zero_check
theorem b51_pivot : b51.v 2=v51 := basis_pivot 125 0x13980139cc0098000000000001398013 2 _ _
def v52 : Space (Fin 125) := wordVector 125 0x13002739801398000000000001300273
theorem v52_self_check : fastDot 125 0x13002739801398000000000001300273 0x13002739801398000000000001300273=1 := by decide
theorem v52_zero_check : bitValue 0x13002739801398000000000001300273 2=0 := by decide
def b52 : OBase (Fin 125) := basis 125 0x13002739801398000000000001300273 2 v52_self_check v52_zero_check
theorem b52_pivot : b52.v 2=v52 := basis_pivot 125 0x13002739801398000000000001300273 2 _ _
def v53 : Space (Fin 125) := wordVector 125 0x1ce700000000000000039ce001ce7
theorem v53_self_check : fastDot 125 0x1ce700000000000000039ce001ce7 0x1ce700000000000000039ce001ce7=1 := by decide
theorem v53_zero_check : bitValue 0x1ce700000000000000039ce001ce7 3=0 := by decide
def b53 : OBase (Fin 125) := basis 125 0x1ce700000000000000039ce001ce7 3 v53_self_check v53_zero_check
theorem b53_pivot : b53.v 3=v53 := basis_pivot 125 0x1ce700000000000000039ce001ce7 3 _ _
def v54 : Space (Fin 125) := wordVector 125 0x7000e70000000000000e001ce7000e7
theorem v54_self_check : fastDot 125 0x7000e70000000000000e001ce7000e7 0x7000e70000000000000e001ce7000e7=1 := by decide
theorem v54_zero_check : bitValue 0x7000e70000000000000e001ce7000e7 3=0 := by decide
def b54 : OBase (Fin 125) := basis 125 0x7000e70000000000000e001ce7000e7 3 v54_self_check v54_zero_check
theorem b54_pivot : b54.v 3=v54 := basis_pivot 125 0x7000e70000000000000e001ce7000e7 3 _ _
def v55 : Space (Fin 125) := wordVector 125 0xd6800d0000000000001ad001ad6800d
theorem v55_self_check : fastDot 125 0xd6800d0000000000001ad001ad6800d 0xd6800d0000000000001ad001ad6800d=1 := by decide
theorem v55_zero_check : bitValue 0xd6800d0000000000001ad001ad6800d 1=0 := by decide
def b55 : OBase (Fin 125) := basis 125 0xd6800d0000000000001ad001ad6800d 1 v55_self_check v55_zero_check
theorem b55_pivot : b55.v 1=v55 := basis_pivot 125 0xd6800d0000000000001ad001ad6800d 1 _ _
def v56 : Space (Fin 125) := wordVector 125 0xce419000000000000019c8320ce419
theorem v56_self_check : fastDot 125 0xce419000000000000019c8320ce419 0xce419000000000000019c8320ce419=1 := by decide
theorem v56_zero_check : bitValue 0xce419000000000000019c8320ce419 1=0 := by decide
def b56 : OBase (Fin 125) := basis 125 0xce419000000000000019c8320ce419 1 v56_self_check v56_zero_check
theorem b56_pivot : b56.v 1=v56 := basis_pivot 125 0xce419000000000000019c8320ce419 1 _ _
def v57 : Space (Fin 125) := wordVector 125 0x19c801900000000000033900339c8019
theorem v57_self_check : fastDot 125 0x19c801900000000000033900339c8019 0x19c801900000000000033900339c8019=1 := by decide
theorem v57_zero_check : bitValue 0x19c801900000000000033900339c8019 1=0 := by decide
def b57 : OBase (Fin 125) := basis 125 0x19c801900000000000033900339c8019 1 v57_self_check v57_zero_check
theorem b57_pivot : b57.v 1=v57 := basis_pivot 125 0x19c801900000000000033900339c8019 1 _ _
def v58 : Space (Fin 125) := wordVector 125 0x19003390000000000003200673900339
theorem v58_self_check : fastDot 125 0x19003390000000000003200673900339 0x19003390000000000003200673900339=1 := by decide
theorem v58_zero_check : bitValue 0x19003390000000000003200673900339 1=0 := by decide
def b58 : OBase (Fin 125) := basis 125 0x19003390000000000003200673900339 1 v58_self_check v58_zero_check
theorem b58_pivot : b58.v 1=v58 := basis_pivot 125 0x19003390000000000003200673900339 1 _ _
def v59 : Space (Fin 125) := wordVector 125 0x9cc13000000000000013982609cc13
theorem v59_self_check : fastDot 125 0x9cc13000000000000013982609cc13 0x9cc13000000000000013982609cc13=1 := by decide
theorem v59_zero_check : bitValue 0x9cc13000000000000013982609cc13 2=0 := by decide
def b59 : OBase (Fin 125) := basis 125 0x9cc13000000000000013982609cc13 2 v59_self_check v59_zero_check
theorem b59_pivot : b59.v 2=v59 := basis_pivot 125 0x9cc13000000000000013982609cc13 2 _ _
def v60 : Space (Fin 125) := wordVector 125 0x13980130000000000002730027398013
theorem v60_self_check : fastDot 125 0x13980130000000000002730027398013 0x13980130000000000002730027398013=1 := by decide
theorem v60_zero_check : bitValue 0x13980130000000000002730027398013 2=0 := by decide
def b60 : OBase (Fin 125) := basis 125 0x13980130000000000002730027398013 2 v60_self_check v60_zero_check
theorem b60_pivot : b60.v 2=v60 := basis_pivot 125 0x13980130000000000002730027398013 2 _ _
def v61 : Space (Fin 125) := wordVector 125 0x130027300000000000026004e7300273
theorem v61_self_check : fastDot 125 0x130027300000000000026004e7300273 0x130027300000000000026004e7300273=1 := by decide
theorem v61_zero_check : bitValue 0x130027300000000000026004e7300273 2=0 := by decide
def b61 : OBase (Fin 125) := basis 125 0x130027300000000000026004e7300273 2 v61_self_check v61_zero_check
theorem b61_pivot : b61.v 2=v61 := basis_pivot 125 0x130027300000000000026004e7300273 2 _ _
def v62 : Space (Fin 125) := wordVector 125 0x1c0039ce001ce7000e7
theorem v62_self_check : fastDot 125 0x1c0039ce001ce7000e7 0x1c0039ce001ce7000e7=1 := by decide
theorem v62_zero_check : bitValue 0x1c0039ce001ce7000e7 3=0 := by decide
def b62 : OBase (Fin 125) := basis 125 0x1c0039ce001ce7000e7 3 v62_self_check v62_zero_check
theorem b62_pivot : b62.v 3=v62 := basis_pivot 125 0x1c0039ce001ce7000e7 3 _ _
def v63 : Space (Fin 125) := wordVector 125 0x1ce001ce7000e738007
theorem v63_self_check : fastDot 125 0x1ce001ce7000e738007 0x1ce001ce7000e738007=1 := by decide
theorem v63_zero_check : bitValue 0x1ce001ce7000e738007 3=0 := by decide
def b63 : OBase (Fin 125) := basis 125 0x1ce001ce7000e738007 3 v63_self_check v63_zero_check
theorem b63_pivot : b63.v 3=v63 := basis_pivot 125 0x1ce001ce7000e738007 3 _ _
end
end FourierSchur.OriginalProjectionNativeDirections
