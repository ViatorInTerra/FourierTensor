import work_in_progress.OriginalProjectionNativeRowCertificate
namespace FourierSchur.OriginalProjectionNativeRowChecks
open OriginalNativeGeneratorSymbols OriginalSparseNativeRows OriginalProjectionNativeRowCertificate
set_option maxHeartbeats 0
set_option maxRecDepth 30000
theorem node_checks_0 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (0+j.val)) rowAt (incomingAt (0+j.val))=rowAt (2048+(0+j.val)) ∧
      (incomingAt (0+j.val)).all (fun p => p.1<2048+(0+j.val))=true) := by decide +kernel
theorem node_checks_32 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (32+j.val)) rowAt (incomingAt (32+j.val))=rowAt (2048+(32+j.val)) ∧
      (incomingAt (32+j.val)).all (fun p => p.1<2048+(32+j.val))=true) := by decide +kernel
theorem node_checks_64 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (64+j.val)) rowAt (incomingAt (64+j.val))=rowAt (2048+(64+j.val)) ∧
      (incomingAt (64+j.val)).all (fun p => p.1<2048+(64+j.val))=true) := by decide +kernel
theorem node_checks_96 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (96+j.val)) rowAt (incomingAt (96+j.val))=rowAt (2048+(96+j.val)) ∧
      (incomingAt (96+j.val)).all (fun p => p.1<2048+(96+j.val))=true) := by decide +kernel
theorem node_checks_128 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (128+j.val)) rowAt (incomingAt (128+j.val))=rowAt (2048+(128+j.val)) ∧
      (incomingAt (128+j.val)).all (fun p => p.1<2048+(128+j.val))=true) := by decide +kernel
theorem node_checks_160 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (160+j.val)) rowAt (incomingAt (160+j.val))=rowAt (2048+(160+j.val)) ∧
      (incomingAt (160+j.val)).all (fun p => p.1<2048+(160+j.val))=true) := by decide +kernel
theorem node_checks_192 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (192+j.val)) rowAt (incomingAt (192+j.val))=rowAt (2048+(192+j.val)) ∧
      (incomingAt (192+j.val)).all (fun p => p.1<2048+(192+j.val))=true) := by decide +kernel
theorem node_checks_224 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (224+j.val)) rowAt (incomingAt (224+j.val))=rowAt (2048+(224+j.val)) ∧
      (incomingAt (224+j.val)).all (fun p => p.1<2048+(224+j.val))=true) := by decide +kernel
theorem node_checks_256 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (256+j.val)) rowAt (incomingAt (256+j.val))=rowAt (2048+(256+j.val)) ∧
      (incomingAt (256+j.val)).all (fun p => p.1<2048+(256+j.val))=true) := by decide +kernel
theorem node_checks_288 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (288+j.val)) rowAt (incomingAt (288+j.val))=rowAt (2048+(288+j.val)) ∧
      (incomingAt (288+j.val)).all (fun p => p.1<2048+(288+j.val))=true) := by decide +kernel
theorem node_checks_320 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (320+j.val)) rowAt (incomingAt (320+j.val))=rowAt (2048+(320+j.val)) ∧
      (incomingAt (320+j.val)).all (fun p => p.1<2048+(320+j.val))=true) := by decide +kernel
theorem node_checks_352 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (352+j.val)) rowAt (incomingAt (352+j.val))=rowAt (2048+(352+j.val)) ∧
      (incomingAt (352+j.val)).all (fun p => p.1<2048+(352+j.val))=true) := by decide +kernel
theorem node_checks_384 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (384+j.val)) rowAt (incomingAt (384+j.val))=rowAt (2048+(384+j.val)) ∧
      (incomingAt (384+j.val)).all (fun p => p.1<2048+(384+j.val))=true) := by decide +kernel
theorem node_checks_416 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (416+j.val)) rowAt (incomingAt (416+j.val))=rowAt (2048+(416+j.val)) ∧
      (incomingAt (416+j.val)).all (fun p => p.1<2048+(416+j.val))=true) := by decide +kernel
theorem node_checks_448 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (448+j.val)) rowAt (incomingAt (448+j.val))=rowAt (2048+(448+j.val)) ∧
      (incomingAt (448+j.val)).all (fun p => p.1<2048+(448+j.val))=true) := by decide +kernel
theorem node_checks_480 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (480+j.val)) rowAt (incomingAt (480+j.val))=rowAt (2048+(480+j.val)) ∧
      (incomingAt (480+j.val)).all (fun p => p.1<2048+(480+j.val))=true) := by decide +kernel
theorem node_checks_512 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (512+j.val)) rowAt (incomingAt (512+j.val))=rowAt (2048+(512+j.val)) ∧
      (incomingAt (512+j.val)).all (fun p => p.1<2048+(512+j.val))=true) := by decide +kernel
theorem node_checks_544 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (544+j.val)) rowAt (incomingAt (544+j.val))=rowAt (2048+(544+j.val)) ∧
      (incomingAt (544+j.val)).all (fun p => p.1<2048+(544+j.val))=true) := by decide +kernel
theorem node_checks_576 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (576+j.val)) rowAt (incomingAt (576+j.val))=rowAt (2048+(576+j.val)) ∧
      (incomingAt (576+j.val)).all (fun p => p.1<2048+(576+j.val))=true) := by decide +kernel
theorem node_checks_608 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (608+j.val)) rowAt (incomingAt (608+j.val))=rowAt (2048+(608+j.val)) ∧
      (incomingAt (608+j.val)).all (fun p => p.1<2048+(608+j.val))=true) := by decide +kernel
theorem node_checks_640 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (640+j.val)) rowAt (incomingAt (640+j.val))=rowAt (2048+(640+j.val)) ∧
      (incomingAt (640+j.val)).all (fun p => p.1<2048+(640+j.val))=true) := by decide +kernel
theorem node_checks_672 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (672+j.val)) rowAt (incomingAt (672+j.val))=rowAt (2048+(672+j.val)) ∧
      (incomingAt (672+j.val)).all (fun p => p.1<2048+(672+j.val))=true) := by decide +kernel
theorem node_checks_704 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (704+j.val)) rowAt (incomingAt (704+j.val))=rowAt (2048+(704+j.val)) ∧
      (incomingAt (704+j.val)).all (fun p => p.1<2048+(704+j.val))=true) := by decide +kernel
theorem node_checks_736 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (736+j.val)) rowAt (incomingAt (736+j.val))=rowAt (2048+(736+j.val)) ∧
      (incomingAt (736+j.val)).all (fun p => p.1<2048+(736+j.val))=true) := by decide +kernel
theorem node_checks_768 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (768+j.val)) rowAt (incomingAt (768+j.val))=rowAt (2048+(768+j.val)) ∧
      (incomingAt (768+j.val)).all (fun p => p.1<2048+(768+j.val))=true) := by decide +kernel
theorem node_checks_800 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (800+j.val)) rowAt (incomingAt (800+j.val))=rowAt (2048+(800+j.val)) ∧
      (incomingAt (800+j.val)).all (fun p => p.1<2048+(800+j.val))=true) := by decide +kernel
theorem node_checks_832 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (832+j.val)) rowAt (incomingAt (832+j.val))=rowAt (2048+(832+j.val)) ∧
      (incomingAt (832+j.val)).all (fun p => p.1<2048+(832+j.val))=true) := by decide +kernel
theorem node_checks_864 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (864+j.val)) rowAt (incomingAt (864+j.val))=rowAt (2048+(864+j.val)) ∧
      (incomingAt (864+j.val)).all (fun p => p.1<2048+(864+j.val))=true) := by decide +kernel
theorem node_checks_896 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (896+j.val)) rowAt (incomingAt (896+j.val))=rowAt (2048+(896+j.val)) ∧
      (incomingAt (896+j.val)).all (fun p => p.1<2048+(896+j.val))=true) := by decide +kernel
theorem node_checks_928 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (928+j.val)) rowAt (incomingAt (928+j.val))=rowAt (2048+(928+j.val)) ∧
      (incomingAt (928+j.val)).all (fun p => p.1<2048+(928+j.val))=true) := by decide +kernel
theorem node_checks_960 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (960+j.val)) rowAt (incomingAt (960+j.val))=rowAt (2048+(960+j.val)) ∧
      (incomingAt (960+j.val)).all (fun p => p.1<2048+(960+j.val))=true) := by decide +kernel
theorem node_checks_992 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (992+j.val)) rowAt (incomingAt (992+j.val))=rowAt (2048+(992+j.val)) ∧
      (incomingAt (992+j.val)).all (fun p => p.1<2048+(992+j.val))=true) := by decide +kernel
theorem node_checks_1024 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (1024+j.val)) rowAt (incomingAt (1024+j.val))=rowAt (2048+(1024+j.val)) ∧
      (incomingAt (1024+j.val)).all (fun p => p.1<2048+(1024+j.val))=true) := by decide +kernel
theorem node_checks_1056 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (1056+j.val)) rowAt (incomingAt (1056+j.val))=rowAt (2048+(1056+j.val)) ∧
      (incomingAt (1056+j.val)).all (fun p => p.1<2048+(1056+j.val))=true) := by decide +kernel
theorem node_checks_1088 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (1088+j.val)) rowAt (incomingAt (1088+j.val))=rowAt (2048+(1088+j.val)) ∧
      (incomingAt (1088+j.val)).all (fun p => p.1<2048+(1088+j.val))=true) := by decide +kernel
theorem node_checks_1120 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (1120+j.val)) rowAt (incomingAt (1120+j.val))=rowAt (2048+(1120+j.val)) ∧
      (incomingAt (1120+j.val)).all (fun p => p.1<2048+(1120+j.val))=true) := by decide +kernel
theorem node_checks_1152 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (1152+j.val)) rowAt (incomingAt (1152+j.val))=rowAt (2048+(1152+j.val)) ∧
      (incomingAt (1152+j.val)).all (fun p => p.1<2048+(1152+j.val))=true) := by decide +kernel
theorem node_checks_1184 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (1184+j.val)) rowAt (incomingAt (1184+j.val))=rowAt (2048+(1184+j.val)) ∧
      (incomingAt (1184+j.val)).all (fun p => p.1<2048+(1184+j.val))=true) := by decide +kernel
theorem node_checks_1216 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (1216+j.val)) rowAt (incomingAt (1216+j.val))=rowAt (2048+(1216+j.val)) ∧
      (incomingAt (1216+j.val)).all (fun p => p.1<2048+(1216+j.val))=true) := by decide +kernel
theorem node_checks_1248 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (1248+j.val)) rowAt (incomingAt (1248+j.val))=rowAt (2048+(1248+j.val)) ∧
      (incomingAt (1248+j.val)).all (fun p => p.1<2048+(1248+j.val))=true) := by decide +kernel
theorem node_checks_1280 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (1280+j.val)) rowAt (incomingAt (1280+j.val))=rowAt (2048+(1280+j.val)) ∧
      (incomingAt (1280+j.val)).all (fun p => p.1<2048+(1280+j.val))=true) := by decide +kernel
theorem node_checks_1312 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (1312+j.val)) rowAt (incomingAt (1312+j.val))=rowAt (2048+(1312+j.val)) ∧
      (incomingAt (1312+j.val)).all (fun p => p.1<2048+(1312+j.val))=true) := by decide +kernel
theorem node_checks_1344 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (1344+j.val)) rowAt (incomingAt (1344+j.val))=rowAt (2048+(1344+j.val)) ∧
      (incomingAt (1344+j.val)).all (fun p => p.1<2048+(1344+j.val))=true) := by decide +kernel
theorem node_checks_1376 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (1376+j.val)) rowAt (incomingAt (1376+j.val))=rowAt (2048+(1376+j.val)) ∧
      (incomingAt (1376+j.val)).all (fun p => p.1<2048+(1376+j.val))=true) := by decide +kernel
theorem node_checks_1408 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (1408+j.val)) rowAt (incomingAt (1408+j.val))=rowAt (2048+(1408+j.val)) ∧
      (incomingAt (1408+j.val)).all (fun p => p.1<2048+(1408+j.val))=true) := by decide +kernel
theorem node_checks_1440 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (1440+j.val)) rowAt (incomingAt (1440+j.val))=rowAt (2048+(1440+j.val)) ∧
      (incomingAt (1440+j.val)).all (fun p => p.1<2048+(1440+j.val))=true) := by decide +kernel
theorem node_checks_1472 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (1472+j.val)) rowAt (incomingAt (1472+j.val))=rowAt (2048+(1472+j.val)) ∧
      (incomingAt (1472+j.val)).all (fun p => p.1<2048+(1472+j.val))=true) := by decide +kernel
theorem node_checks_1504 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (1504+j.val)) rowAt (incomingAt (1504+j.val))=rowAt (2048+(1504+j.val)) ∧
      (incomingAt (1504+j.val)).all (fun p => p.1<2048+(1504+j.val))=true) := by decide +kernel
theorem node_checks_1536 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (1536+j.val)) rowAt (incomingAt (1536+j.val))=rowAt (2048+(1536+j.val)) ∧
      (incomingAt (1536+j.val)).all (fun p => p.1<2048+(1536+j.val))=true) := by decide +kernel
theorem node_checks_1568 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (1568+j.val)) rowAt (incomingAt (1568+j.val))=rowAt (2048+(1568+j.val)) ∧
      (incomingAt (1568+j.val)).all (fun p => p.1<2048+(1568+j.val))=true) := by decide +kernel
theorem node_checks_1600 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (1600+j.val)) rowAt (incomingAt (1600+j.val))=rowAt (2048+(1600+j.val)) ∧
      (incomingAt (1600+j.val)).all (fun p => p.1<2048+(1600+j.val))=true) := by decide +kernel
theorem node_checks_1632 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (1632+j.val)) rowAt (incomingAt (1632+j.val))=rowAt (2048+(1632+j.val)) ∧
      (incomingAt (1632+j.val)).all (fun p => p.1<2048+(1632+j.val))=true) := by decide +kernel
theorem node_checks_1664 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (1664+j.val)) rowAt (incomingAt (1664+j.val))=rowAt (2048+(1664+j.val)) ∧
      (incomingAt (1664+j.val)).all (fun p => p.1<2048+(1664+j.val))=true) := by decide +kernel
theorem node_checks_1696 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (1696+j.val)) rowAt (incomingAt (1696+j.val))=rowAt (2048+(1696+j.val)) ∧
      (incomingAt (1696+j.val)).all (fun p => p.1<2048+(1696+j.val))=true) := by decide +kernel
theorem node_checks_1728 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (1728+j.val)) rowAt (incomingAt (1728+j.val))=rowAt (2048+(1728+j.val)) ∧
      (incomingAt (1728+j.val)).all (fun p => p.1<2048+(1728+j.val))=true) := by decide +kernel
theorem node_checks_1760 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (1760+j.val)) rowAt (incomingAt (1760+j.val))=rowAt (2048+(1760+j.val)) ∧
      (incomingAt (1760+j.val)).all (fun p => p.1<2048+(1760+j.val))=true) := by decide +kernel
theorem node_checks_1792 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (1792+j.val)) rowAt (incomingAt (1792+j.val))=rowAt (2048+(1792+j.val)) ∧
      (incomingAt (1792+j.val)).all (fun p => p.1<2048+(1792+j.val))=true) := by decide +kernel
theorem node_checks_1824 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (1824+j.val)) rowAt (incomingAt (1824+j.val))=rowAt (2048+(1824+j.val)) ∧
      (incomingAt (1824+j.val)).all (fun p => p.1<2048+(1824+j.val))=true) := by decide +kernel
theorem node_checks_1856 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (1856+j.val)) rowAt (incomingAt (1856+j.val))=rowAt (2048+(1856+j.val)) ∧
      (incomingAt (1856+j.val)).all (fun p => p.1<2048+(1856+j.val))=true) := by decide +kernel
theorem node_checks_1888 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (1888+j.val)) rowAt (incomingAt (1888+j.val))=rowAt (2048+(1888+j.val)) ∧
      (incomingAt (1888+j.val)).all (fun p => p.1<2048+(1888+j.val))=true) := by decide +kernel
theorem node_checks_1920 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (1920+j.val)) rowAt (incomingAt (1920+j.val))=rowAt (2048+(1920+j.val)) ∧
      (incomingAt (1920+j.val)).all (fun p => p.1<2048+(1920+j.val))=true) := by decide +kernel
theorem node_checks_1952 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (1952+j.val)) rowAt (incomingAt (1952+j.val))=rowAt (2048+(1952+j.val)) ∧
      (incomingAt (1952+j.val)).all (fun p => p.1<2048+(1952+j.val))=true) := by decide +kernel
theorem node_checks_1984 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (1984+j.val)) rowAt (incomingAt (1984+j.val))=rowAt (2048+(1984+j.val)) ∧
      (incomingAt (1984+j.val)).all (fun p => p.1<2048+(1984+j.val))=true) := by decide +kernel
theorem node_checks_2016 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (2016+j.val)) rowAt (incomingAt (2016+j.val))=rowAt (2048+(2016+j.val)) ∧
      (incomingAt (2016+j.val)).all (fun p => p.1<2048+(2016+j.val))=true) := by decide +kernel
theorem node_checks_2048 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (2048+j.val)) rowAt (incomingAt (2048+j.val))=rowAt (2048+(2048+j.val)) ∧
      (incomingAt (2048+j.val)).all (fun p => p.1<2048+(2048+j.val))=true) := by decide +kernel
theorem node_checks_2080 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (2080+j.val)) rowAt (incomingAt (2080+j.val))=rowAt (2048+(2080+j.val)) ∧
      (incomingAt (2080+j.val)).all (fun p => p.1<2048+(2080+j.val))=true) := by decide +kernel
theorem node_checks_2112 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (2112+j.val)) rowAt (incomingAt (2112+j.val))=rowAt (2048+(2112+j.val)) ∧
      (incomingAt (2112+j.val)).all (fun p => p.1<2048+(2112+j.val))=true) := by decide +kernel
theorem node_checks_2144 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (2144+j.val)) rowAt (incomingAt (2144+j.val))=rowAt (2048+(2144+j.val)) ∧
      (incomingAt (2144+j.val)).all (fun p => p.1<2048+(2144+j.val))=true) := by decide +kernel
theorem node_checks_2176 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (2176+j.val)) rowAt (incomingAt (2176+j.val))=rowAt (2048+(2176+j.val)) ∧
      (incomingAt (2176+j.val)).all (fun p => p.1<2048+(2176+j.val))=true) := by decide +kernel
theorem node_checks_2208 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (2208+j.val)) rowAt (incomingAt (2208+j.val))=rowAt (2048+(2208+j.val)) ∧
      (incomingAt (2208+j.val)).all (fun p => p.1<2048+(2208+j.val))=true) := by decide +kernel
theorem node_checks_2240 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (2240+j.val)) rowAt (incomingAt (2240+j.val))=rowAt (2048+(2240+j.val)) ∧
      (incomingAt (2240+j.val)).all (fun p => p.1<2048+(2240+j.val))=true) := by decide +kernel
theorem node_checks_2272 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (2272+j.val)) rowAt (incomingAt (2272+j.val))=rowAt (2048+(2272+j.val)) ∧
      (incomingAt (2272+j.val)).all (fun p => p.1<2048+(2272+j.val))=true) := by decide +kernel
theorem node_checks_2304 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (2304+j.val)) rowAt (incomingAt (2304+j.val))=rowAt (2048+(2304+j.val)) ∧
      (incomingAt (2304+j.val)).all (fun p => p.1<2048+(2304+j.val))=true) := by decide +kernel
theorem node_checks_2336 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (2336+j.val)) rowAt (incomingAt (2336+j.val))=rowAt (2048+(2336+j.val)) ∧
      (incomingAt (2336+j.val)).all (fun p => p.1<2048+(2336+j.val))=true) := by decide +kernel
theorem node_checks_2368 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (2368+j.val)) rowAt (incomingAt (2368+j.val))=rowAt (2048+(2368+j.val)) ∧
      (incomingAt (2368+j.val)).all (fun p => p.1<2048+(2368+j.val))=true) := by decide +kernel
theorem node_checks_2400 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (2400+j.val)) rowAt (incomingAt (2400+j.val))=rowAt (2048+(2400+j.val)) ∧
      (incomingAt (2400+j.val)).all (fun p => p.1<2048+(2400+j.val))=true) := by decide +kernel
theorem node_checks_2432 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (2432+j.val)) rowAt (incomingAt (2432+j.val))=rowAt (2048+(2432+j.val)) ∧
      (incomingAt (2432+j.val)).all (fun p => p.1<2048+(2432+j.val))=true) := by decide +kernel
theorem node_checks_2464 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (2464+j.val)) rowAt (incomingAt (2464+j.val))=rowAt (2048+(2464+j.val)) ∧
      (incomingAt (2464+j.val)).all (fun p => p.1<2048+(2464+j.val))=true) := by decide +kernel
theorem node_checks_2496 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (2496+j.val)) rowAt (incomingAt (2496+j.val))=rowAt (2048+(2496+j.val)) ∧
      (incomingAt (2496+j.val)).all (fun p => p.1<2048+(2496+j.val))=true) := by decide +kernel
theorem node_checks_2528 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (2528+j.val)) rowAt (incomingAt (2528+j.val))=rowAt (2048+(2528+j.val)) ∧
      (incomingAt (2528+j.val)).all (fun p => p.1<2048+(2528+j.val))=true) := by decide +kernel
theorem node_checks_2560 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (2560+j.val)) rowAt (incomingAt (2560+j.val))=rowAt (2048+(2560+j.val)) ∧
      (incomingAt (2560+j.val)).all (fun p => p.1<2048+(2560+j.val))=true) := by decide +kernel
theorem node_checks_2592 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (2592+j.val)) rowAt (incomingAt (2592+j.val))=rowAt (2048+(2592+j.val)) ∧
      (incomingAt (2592+j.val)).all (fun p => p.1<2048+(2592+j.val))=true) := by decide +kernel
theorem node_checks_2624 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (2624+j.val)) rowAt (incomingAt (2624+j.val))=rowAt (2048+(2624+j.val)) ∧
      (incomingAt (2624+j.val)).all (fun p => p.1<2048+(2624+j.val))=true) := by decide +kernel
theorem node_checks_2656 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (2656+j.val)) rowAt (incomingAt (2656+j.val))=rowAt (2048+(2656+j.val)) ∧
      (incomingAt (2656+j.val)).all (fun p => p.1<2048+(2656+j.val))=true) := by decide +kernel
theorem node_checks_2688 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (2688+j.val)) rowAt (incomingAt (2688+j.val))=rowAt (2048+(2688+j.val)) ∧
      (incomingAt (2688+j.val)).all (fun p => p.1<2048+(2688+j.val))=true) := by decide +kernel
theorem node_checks_2720 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (2720+j.val)) rowAt (incomingAt (2720+j.val))=rowAt (2048+(2720+j.val)) ∧
      (incomingAt (2720+j.val)).all (fun p => p.1<2048+(2720+j.val))=true) := by decide +kernel
theorem node_checks_2752 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (2752+j.val)) rowAt (incomingAt (2752+j.val))=rowAt (2048+(2752+j.val)) ∧
      (incomingAt (2752+j.val)).all (fun p => p.1<2048+(2752+j.val))=true) := by decide +kernel
theorem node_checks_2784 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (2784+j.val)) rowAt (incomingAt (2784+j.val))=rowAt (2048+(2784+j.val)) ∧
      (incomingAt (2784+j.val)).all (fun p => p.1<2048+(2784+j.val))=true) := by decide +kernel
theorem node_checks_2816 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (2816+j.val)) rowAt (incomingAt (2816+j.val))=rowAt (2048+(2816+j.val)) ∧
      (incomingAt (2816+j.val)).all (fun p => p.1<2048+(2816+j.val))=true) := by decide +kernel
theorem node_checks_2848 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (2848+j.val)) rowAt (incomingAt (2848+j.val))=rowAt (2048+(2848+j.val)) ∧
      (incomingAt (2848+j.val)).all (fun p => p.1<2048+(2848+j.val))=true) := by decide +kernel
theorem node_checks_2880 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (2880+j.val)) rowAt (incomingAt (2880+j.val))=rowAt (2048+(2880+j.val)) ∧
      (incomingAt (2880+j.val)).all (fun p => p.1<2048+(2880+j.val))=true) := by decide +kernel
theorem node_checks_2912 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (2912+j.val)) rowAt (incomingAt (2912+j.val))=rowAt (2048+(2912+j.val)) ∧
      (incomingAt (2912+j.val)).all (fun p => p.1<2048+(2912+j.val))=true) := by decide +kernel
theorem node_checks_2944 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (2944+j.val)) rowAt (incomingAt (2944+j.val))=rowAt (2048+(2944+j.val)) ∧
      (incomingAt (2944+j.val)).all (fun p => p.1<2048+(2944+j.val))=true) := by decide +kernel
theorem node_checks_2976 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (2976+j.val)) rowAt (incomingAt (2976+j.val))=rowAt (2048+(2976+j.val)) ∧
      (incomingAt (2976+j.val)).all (fun p => p.1<2048+(2976+j.val))=true) := by decide +kernel
theorem node_checks_3008 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (3008+j.val)) rowAt (incomingAt (3008+j.val))=rowAt (2048+(3008+j.val)) ∧
      (incomingAt (3008+j.val)).all (fun p => p.1<2048+(3008+j.val))=true) := by decide +kernel
theorem node_checks_3040 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (3040+j.val)) rowAt (incomingAt (3040+j.val))=rowAt (2048+(3040+j.val)) ∧
      (incomingAt (3040+j.val)).all (fun p => p.1<2048+(3040+j.val))=true) := by decide +kernel
theorem node_checks_3072 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (3072+j.val)) rowAt (incomingAt (3072+j.val))=rowAt (2048+(3072+j.val)) ∧
      (incomingAt (3072+j.val)).all (fun p => p.1<2048+(3072+j.val))=true) := by decide +kernel
theorem node_checks_3104 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (3104+j.val)) rowAt (incomingAt (3104+j.val))=rowAt (2048+(3104+j.val)) ∧
      (incomingAt (3104+j.val)).all (fun p => p.1<2048+(3104+j.val))=true) := by decide +kernel
theorem node_checks_3136 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (3136+j.val)) rowAt (incomingAt (3136+j.val))=rowAt (2048+(3136+j.val)) ∧
      (incomingAt (3136+j.val)).all (fun p => p.1<2048+(3136+j.val))=true) := by decide +kernel
theorem node_checks_3168 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (3168+j.val)) rowAt (incomingAt (3168+j.val))=rowAt (2048+(3168+j.val)) ∧
      (incomingAt (3168+j.val)).all (fun p => p.1<2048+(3168+j.val))=true) := by decide +kernel
theorem node_checks_3200 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (3200+j.val)) rowAt (incomingAt (3200+j.val))=rowAt (2048+(3200+j.val)) ∧
      (incomingAt (3200+j.val)).all (fun p => p.1<2048+(3200+j.val))=true) := by decide +kernel
theorem node_checks_3232 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (3232+j.val)) rowAt (incomingAt (3232+j.val))=rowAt (2048+(3232+j.val)) ∧
      (incomingAt (3232+j.val)).all (fun p => p.1<2048+(3232+j.val))=true) := by decide +kernel
theorem node_checks_3264 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (3264+j.val)) rowAt (incomingAt (3264+j.val))=rowAt (2048+(3264+j.val)) ∧
      (incomingAt (3264+j.val)).all (fun p => p.1<2048+(3264+j.val))=true) := by decide +kernel
theorem node_checks_3296 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (3296+j.val)) rowAt (incomingAt (3296+j.val))=rowAt (2048+(3296+j.val)) ∧
      (incomingAt (3296+j.val)).all (fun p => p.1<2048+(3296+j.val))=true) := by decide +kernel
theorem node_checks_3328 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (3328+j.val)) rowAt (incomingAt (3328+j.val))=rowAt (2048+(3328+j.val)) ∧
      (incomingAt (3328+j.val)).all (fun p => p.1<2048+(3328+j.val))=true) := by decide +kernel
theorem node_checks_3360 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (3360+j.val)) rowAt (incomingAt (3360+j.val))=rowAt (2048+(3360+j.val)) ∧
      (incomingAt (3360+j.val)).all (fun p => p.1<2048+(3360+j.val))=true) := by decide +kernel
theorem node_checks_3392 : ∀ j : Fin 32,
    (nextRow directions (phaseAt (3392+j.val)) rowAt (incomingAt (3392+j.val))=rowAt (2048+(3392+j.val)) ∧
      (incomingAt (3392+j.val)).all (fun p => p.1<2048+(3392+j.val))=true) := by decide +kernel
theorem node_checks_3424 : ∀ j : Fin 23,
    (nextRow directions (phaseAt (3424+j.val)) rowAt (incomingAt (3424+j.val))=rowAt (2048+(3424+j.val)) ∧
      (incomingAt (3424+j.val)).all (fun p => p.1<2048+(3424+j.val))=true) := by decide +kernel
theorem node_checks (i : Fin 3447) : (nextRow directions (phaseAt i.val) rowAt (incomingAt i.val)=rowAt (2048+i.val) ∧
      (incomingAt i.val).all (fun p => p.1<2048+i.val)=true) := by
  by_cases h0 : i.val<32
  · have he : 0+(i.val-0)=i.val := by omega
    simpa only [he] using node_checks_0 ⟨i.val-0,by omega⟩
  by_cases h32 : i.val<64
  · have he : 32+(i.val-32)=i.val := by omega
    simpa only [he] using node_checks_32 ⟨i.val-32,by omega⟩
  by_cases h64 : i.val<96
  · have he : 64+(i.val-64)=i.val := by omega
    simpa only [he] using node_checks_64 ⟨i.val-64,by omega⟩
  by_cases h96 : i.val<128
  · have he : 96+(i.val-96)=i.val := by omega
    simpa only [he] using node_checks_96 ⟨i.val-96,by omega⟩
  by_cases h128 : i.val<160
  · have he : 128+(i.val-128)=i.val := by omega
    simpa only [he] using node_checks_128 ⟨i.val-128,by omega⟩
  by_cases h160 : i.val<192
  · have he : 160+(i.val-160)=i.val := by omega
    simpa only [he] using node_checks_160 ⟨i.val-160,by omega⟩
  by_cases h192 : i.val<224
  · have he : 192+(i.val-192)=i.val := by omega
    simpa only [he] using node_checks_192 ⟨i.val-192,by omega⟩
  by_cases h224 : i.val<256
  · have he : 224+(i.val-224)=i.val := by omega
    simpa only [he] using node_checks_224 ⟨i.val-224,by omega⟩
  by_cases h256 : i.val<288
  · have he : 256+(i.val-256)=i.val := by omega
    simpa only [he] using node_checks_256 ⟨i.val-256,by omega⟩
  by_cases h288 : i.val<320
  · have he : 288+(i.val-288)=i.val := by omega
    simpa only [he] using node_checks_288 ⟨i.val-288,by omega⟩
  by_cases h320 : i.val<352
  · have he : 320+(i.val-320)=i.val := by omega
    simpa only [he] using node_checks_320 ⟨i.val-320,by omega⟩
  by_cases h352 : i.val<384
  · have he : 352+(i.val-352)=i.val := by omega
    simpa only [he] using node_checks_352 ⟨i.val-352,by omega⟩
  by_cases h384 : i.val<416
  · have he : 384+(i.val-384)=i.val := by omega
    simpa only [he] using node_checks_384 ⟨i.val-384,by omega⟩
  by_cases h416 : i.val<448
  · have he : 416+(i.val-416)=i.val := by omega
    simpa only [he] using node_checks_416 ⟨i.val-416,by omega⟩
  by_cases h448 : i.val<480
  · have he : 448+(i.val-448)=i.val := by omega
    simpa only [he] using node_checks_448 ⟨i.val-448,by omega⟩
  by_cases h480 : i.val<512
  · have he : 480+(i.val-480)=i.val := by omega
    simpa only [he] using node_checks_480 ⟨i.val-480,by omega⟩
  by_cases h512 : i.val<544
  · have he : 512+(i.val-512)=i.val := by omega
    simpa only [he] using node_checks_512 ⟨i.val-512,by omega⟩
  by_cases h544 : i.val<576
  · have he : 544+(i.val-544)=i.val := by omega
    simpa only [he] using node_checks_544 ⟨i.val-544,by omega⟩
  by_cases h576 : i.val<608
  · have he : 576+(i.val-576)=i.val := by omega
    simpa only [he] using node_checks_576 ⟨i.val-576,by omega⟩
  by_cases h608 : i.val<640
  · have he : 608+(i.val-608)=i.val := by omega
    simpa only [he] using node_checks_608 ⟨i.val-608,by omega⟩
  by_cases h640 : i.val<672
  · have he : 640+(i.val-640)=i.val := by omega
    simpa only [he] using node_checks_640 ⟨i.val-640,by omega⟩
  by_cases h672 : i.val<704
  · have he : 672+(i.val-672)=i.val := by omega
    simpa only [he] using node_checks_672 ⟨i.val-672,by omega⟩
  by_cases h704 : i.val<736
  · have he : 704+(i.val-704)=i.val := by omega
    simpa only [he] using node_checks_704 ⟨i.val-704,by omega⟩
  by_cases h736 : i.val<768
  · have he : 736+(i.val-736)=i.val := by omega
    simpa only [he] using node_checks_736 ⟨i.val-736,by omega⟩
  by_cases h768 : i.val<800
  · have he : 768+(i.val-768)=i.val := by omega
    simpa only [he] using node_checks_768 ⟨i.val-768,by omega⟩
  by_cases h800 : i.val<832
  · have he : 800+(i.val-800)=i.val := by omega
    simpa only [he] using node_checks_800 ⟨i.val-800,by omega⟩
  by_cases h832 : i.val<864
  · have he : 832+(i.val-832)=i.val := by omega
    simpa only [he] using node_checks_832 ⟨i.val-832,by omega⟩
  by_cases h864 : i.val<896
  · have he : 864+(i.val-864)=i.val := by omega
    simpa only [he] using node_checks_864 ⟨i.val-864,by omega⟩
  by_cases h896 : i.val<928
  · have he : 896+(i.val-896)=i.val := by omega
    simpa only [he] using node_checks_896 ⟨i.val-896,by omega⟩
  by_cases h928 : i.val<960
  · have he : 928+(i.val-928)=i.val := by omega
    simpa only [he] using node_checks_928 ⟨i.val-928,by omega⟩
  by_cases h960 : i.val<992
  · have he : 960+(i.val-960)=i.val := by omega
    simpa only [he] using node_checks_960 ⟨i.val-960,by omega⟩
  by_cases h992 : i.val<1024
  · have he : 992+(i.val-992)=i.val := by omega
    simpa only [he] using node_checks_992 ⟨i.val-992,by omega⟩
  by_cases h1024 : i.val<1056
  · have he : 1024+(i.val-1024)=i.val := by omega
    simpa only [he] using node_checks_1024 ⟨i.val-1024,by omega⟩
  by_cases h1056 : i.val<1088
  · have he : 1056+(i.val-1056)=i.val := by omega
    simpa only [he] using node_checks_1056 ⟨i.val-1056,by omega⟩
  by_cases h1088 : i.val<1120
  · have he : 1088+(i.val-1088)=i.val := by omega
    simpa only [he] using node_checks_1088 ⟨i.val-1088,by omega⟩
  by_cases h1120 : i.val<1152
  · have he : 1120+(i.val-1120)=i.val := by omega
    simpa only [he] using node_checks_1120 ⟨i.val-1120,by omega⟩
  by_cases h1152 : i.val<1184
  · have he : 1152+(i.val-1152)=i.val := by omega
    simpa only [he] using node_checks_1152 ⟨i.val-1152,by omega⟩
  by_cases h1184 : i.val<1216
  · have he : 1184+(i.val-1184)=i.val := by omega
    simpa only [he] using node_checks_1184 ⟨i.val-1184,by omega⟩
  by_cases h1216 : i.val<1248
  · have he : 1216+(i.val-1216)=i.val := by omega
    simpa only [he] using node_checks_1216 ⟨i.val-1216,by omega⟩
  by_cases h1248 : i.val<1280
  · have he : 1248+(i.val-1248)=i.val := by omega
    simpa only [he] using node_checks_1248 ⟨i.val-1248,by omega⟩
  by_cases h1280 : i.val<1312
  · have he : 1280+(i.val-1280)=i.val := by omega
    simpa only [he] using node_checks_1280 ⟨i.val-1280,by omega⟩
  by_cases h1312 : i.val<1344
  · have he : 1312+(i.val-1312)=i.val := by omega
    simpa only [he] using node_checks_1312 ⟨i.val-1312,by omega⟩
  by_cases h1344 : i.val<1376
  · have he : 1344+(i.val-1344)=i.val := by omega
    simpa only [he] using node_checks_1344 ⟨i.val-1344,by omega⟩
  by_cases h1376 : i.val<1408
  · have he : 1376+(i.val-1376)=i.val := by omega
    simpa only [he] using node_checks_1376 ⟨i.val-1376,by omega⟩
  by_cases h1408 : i.val<1440
  · have he : 1408+(i.val-1408)=i.val := by omega
    simpa only [he] using node_checks_1408 ⟨i.val-1408,by omega⟩
  by_cases h1440 : i.val<1472
  · have he : 1440+(i.val-1440)=i.val := by omega
    simpa only [he] using node_checks_1440 ⟨i.val-1440,by omega⟩
  by_cases h1472 : i.val<1504
  · have he : 1472+(i.val-1472)=i.val := by omega
    simpa only [he] using node_checks_1472 ⟨i.val-1472,by omega⟩
  by_cases h1504 : i.val<1536
  · have he : 1504+(i.val-1504)=i.val := by omega
    simpa only [he] using node_checks_1504 ⟨i.val-1504,by omega⟩
  by_cases h1536 : i.val<1568
  · have he : 1536+(i.val-1536)=i.val := by omega
    simpa only [he] using node_checks_1536 ⟨i.val-1536,by omega⟩
  by_cases h1568 : i.val<1600
  · have he : 1568+(i.val-1568)=i.val := by omega
    simpa only [he] using node_checks_1568 ⟨i.val-1568,by omega⟩
  by_cases h1600 : i.val<1632
  · have he : 1600+(i.val-1600)=i.val := by omega
    simpa only [he] using node_checks_1600 ⟨i.val-1600,by omega⟩
  by_cases h1632 : i.val<1664
  · have he : 1632+(i.val-1632)=i.val := by omega
    simpa only [he] using node_checks_1632 ⟨i.val-1632,by omega⟩
  by_cases h1664 : i.val<1696
  · have he : 1664+(i.val-1664)=i.val := by omega
    simpa only [he] using node_checks_1664 ⟨i.val-1664,by omega⟩
  by_cases h1696 : i.val<1728
  · have he : 1696+(i.val-1696)=i.val := by omega
    simpa only [he] using node_checks_1696 ⟨i.val-1696,by omega⟩
  by_cases h1728 : i.val<1760
  · have he : 1728+(i.val-1728)=i.val := by omega
    simpa only [he] using node_checks_1728 ⟨i.val-1728,by omega⟩
  by_cases h1760 : i.val<1792
  · have he : 1760+(i.val-1760)=i.val := by omega
    simpa only [he] using node_checks_1760 ⟨i.val-1760,by omega⟩
  by_cases h1792 : i.val<1824
  · have he : 1792+(i.val-1792)=i.val := by omega
    simpa only [he] using node_checks_1792 ⟨i.val-1792,by omega⟩
  by_cases h1824 : i.val<1856
  · have he : 1824+(i.val-1824)=i.val := by omega
    simpa only [he] using node_checks_1824 ⟨i.val-1824,by omega⟩
  by_cases h1856 : i.val<1888
  · have he : 1856+(i.val-1856)=i.val := by omega
    simpa only [he] using node_checks_1856 ⟨i.val-1856,by omega⟩
  by_cases h1888 : i.val<1920
  · have he : 1888+(i.val-1888)=i.val := by omega
    simpa only [he] using node_checks_1888 ⟨i.val-1888,by omega⟩
  by_cases h1920 : i.val<1952
  · have he : 1920+(i.val-1920)=i.val := by omega
    simpa only [he] using node_checks_1920 ⟨i.val-1920,by omega⟩
  by_cases h1952 : i.val<1984
  · have he : 1952+(i.val-1952)=i.val := by omega
    simpa only [he] using node_checks_1952 ⟨i.val-1952,by omega⟩
  by_cases h1984 : i.val<2016
  · have he : 1984+(i.val-1984)=i.val := by omega
    simpa only [he] using node_checks_1984 ⟨i.val-1984,by omega⟩
  by_cases h2016 : i.val<2048
  · have he : 2016+(i.val-2016)=i.val := by omega
    simpa only [he] using node_checks_2016 ⟨i.val-2016,by omega⟩
  by_cases h2048 : i.val<2080
  · have he : 2048+(i.val-2048)=i.val := by omega
    simpa only [he] using node_checks_2048 ⟨i.val-2048,by omega⟩
  by_cases h2080 : i.val<2112
  · have he : 2080+(i.val-2080)=i.val := by omega
    simpa only [he] using node_checks_2080 ⟨i.val-2080,by omega⟩
  by_cases h2112 : i.val<2144
  · have he : 2112+(i.val-2112)=i.val := by omega
    simpa only [he] using node_checks_2112 ⟨i.val-2112,by omega⟩
  by_cases h2144 : i.val<2176
  · have he : 2144+(i.val-2144)=i.val := by omega
    simpa only [he] using node_checks_2144 ⟨i.val-2144,by omega⟩
  by_cases h2176 : i.val<2208
  · have he : 2176+(i.val-2176)=i.val := by omega
    simpa only [he] using node_checks_2176 ⟨i.val-2176,by omega⟩
  by_cases h2208 : i.val<2240
  · have he : 2208+(i.val-2208)=i.val := by omega
    simpa only [he] using node_checks_2208 ⟨i.val-2208,by omega⟩
  by_cases h2240 : i.val<2272
  · have he : 2240+(i.val-2240)=i.val := by omega
    simpa only [he] using node_checks_2240 ⟨i.val-2240,by omega⟩
  by_cases h2272 : i.val<2304
  · have he : 2272+(i.val-2272)=i.val := by omega
    simpa only [he] using node_checks_2272 ⟨i.val-2272,by omega⟩
  by_cases h2304 : i.val<2336
  · have he : 2304+(i.val-2304)=i.val := by omega
    simpa only [he] using node_checks_2304 ⟨i.val-2304,by omega⟩
  by_cases h2336 : i.val<2368
  · have he : 2336+(i.val-2336)=i.val := by omega
    simpa only [he] using node_checks_2336 ⟨i.val-2336,by omega⟩
  by_cases h2368 : i.val<2400
  · have he : 2368+(i.val-2368)=i.val := by omega
    simpa only [he] using node_checks_2368 ⟨i.val-2368,by omega⟩
  by_cases h2400 : i.val<2432
  · have he : 2400+(i.val-2400)=i.val := by omega
    simpa only [he] using node_checks_2400 ⟨i.val-2400,by omega⟩
  by_cases h2432 : i.val<2464
  · have he : 2432+(i.val-2432)=i.val := by omega
    simpa only [he] using node_checks_2432 ⟨i.val-2432,by omega⟩
  by_cases h2464 : i.val<2496
  · have he : 2464+(i.val-2464)=i.val := by omega
    simpa only [he] using node_checks_2464 ⟨i.val-2464,by omega⟩
  by_cases h2496 : i.val<2528
  · have he : 2496+(i.val-2496)=i.val := by omega
    simpa only [he] using node_checks_2496 ⟨i.val-2496,by omega⟩
  by_cases h2528 : i.val<2560
  · have he : 2528+(i.val-2528)=i.val := by omega
    simpa only [he] using node_checks_2528 ⟨i.val-2528,by omega⟩
  by_cases h2560 : i.val<2592
  · have he : 2560+(i.val-2560)=i.val := by omega
    simpa only [he] using node_checks_2560 ⟨i.val-2560,by omega⟩
  by_cases h2592 : i.val<2624
  · have he : 2592+(i.val-2592)=i.val := by omega
    simpa only [he] using node_checks_2592 ⟨i.val-2592,by omega⟩
  by_cases h2624 : i.val<2656
  · have he : 2624+(i.val-2624)=i.val := by omega
    simpa only [he] using node_checks_2624 ⟨i.val-2624,by omega⟩
  by_cases h2656 : i.val<2688
  · have he : 2656+(i.val-2656)=i.val := by omega
    simpa only [he] using node_checks_2656 ⟨i.val-2656,by omega⟩
  by_cases h2688 : i.val<2720
  · have he : 2688+(i.val-2688)=i.val := by omega
    simpa only [he] using node_checks_2688 ⟨i.val-2688,by omega⟩
  by_cases h2720 : i.val<2752
  · have he : 2720+(i.val-2720)=i.val := by omega
    simpa only [he] using node_checks_2720 ⟨i.val-2720,by omega⟩
  by_cases h2752 : i.val<2784
  · have he : 2752+(i.val-2752)=i.val := by omega
    simpa only [he] using node_checks_2752 ⟨i.val-2752,by omega⟩
  by_cases h2784 : i.val<2816
  · have he : 2784+(i.val-2784)=i.val := by omega
    simpa only [he] using node_checks_2784 ⟨i.val-2784,by omega⟩
  by_cases h2816 : i.val<2848
  · have he : 2816+(i.val-2816)=i.val := by omega
    simpa only [he] using node_checks_2816 ⟨i.val-2816,by omega⟩
  by_cases h2848 : i.val<2880
  · have he : 2848+(i.val-2848)=i.val := by omega
    simpa only [he] using node_checks_2848 ⟨i.val-2848,by omega⟩
  by_cases h2880 : i.val<2912
  · have he : 2880+(i.val-2880)=i.val := by omega
    simpa only [he] using node_checks_2880 ⟨i.val-2880,by omega⟩
  by_cases h2912 : i.val<2944
  · have he : 2912+(i.val-2912)=i.val := by omega
    simpa only [he] using node_checks_2912 ⟨i.val-2912,by omega⟩
  by_cases h2944 : i.val<2976
  · have he : 2944+(i.val-2944)=i.val := by omega
    simpa only [he] using node_checks_2944 ⟨i.val-2944,by omega⟩
  by_cases h2976 : i.val<3008
  · have he : 2976+(i.val-2976)=i.val := by omega
    simpa only [he] using node_checks_2976 ⟨i.val-2976,by omega⟩
  by_cases h3008 : i.val<3040
  · have he : 3008+(i.val-3008)=i.val := by omega
    simpa only [he] using node_checks_3008 ⟨i.val-3008,by omega⟩
  by_cases h3040 : i.val<3072
  · have he : 3040+(i.val-3040)=i.val := by omega
    simpa only [he] using node_checks_3040 ⟨i.val-3040,by omega⟩
  by_cases h3072 : i.val<3104
  · have he : 3072+(i.val-3072)=i.val := by omega
    simpa only [he] using node_checks_3072 ⟨i.val-3072,by omega⟩
  by_cases h3104 : i.val<3136
  · have he : 3104+(i.val-3104)=i.val := by omega
    simpa only [he] using node_checks_3104 ⟨i.val-3104,by omega⟩
  by_cases h3136 : i.val<3168
  · have he : 3136+(i.val-3136)=i.val := by omega
    simpa only [he] using node_checks_3136 ⟨i.val-3136,by omega⟩
  by_cases h3168 : i.val<3200
  · have he : 3168+(i.val-3168)=i.val := by omega
    simpa only [he] using node_checks_3168 ⟨i.val-3168,by omega⟩
  by_cases h3200 : i.val<3232
  · have he : 3200+(i.val-3200)=i.val := by omega
    simpa only [he] using node_checks_3200 ⟨i.val-3200,by omega⟩
  by_cases h3232 : i.val<3264
  · have he : 3232+(i.val-3232)=i.val := by omega
    simpa only [he] using node_checks_3232 ⟨i.val-3232,by omega⟩
  by_cases h3264 : i.val<3296
  · have he : 3264+(i.val-3264)=i.val := by omega
    simpa only [he] using node_checks_3264 ⟨i.val-3264,by omega⟩
  by_cases h3296 : i.val<3328
  · have he : 3296+(i.val-3296)=i.val := by omega
    simpa only [he] using node_checks_3296 ⟨i.val-3296,by omega⟩
  by_cases h3328 : i.val<3360
  · have he : 3328+(i.val-3328)=i.val := by omega
    simpa only [he] using node_checks_3328 ⟨i.val-3328,by omega⟩
  by_cases h3360 : i.val<3392
  · have he : 3360+(i.val-3360)=i.val := by omega
    simpa only [he] using node_checks_3360 ⟨i.val-3360,by omega⟩
  by_cases h3392 : i.val<3424
  · have he : 3392+(i.val-3392)=i.val := by omega
    simpa only [he] using node_checks_3392 ⟨i.val-3392,by omega⟩
  have he : 3424+(i.val-3424)=i.val := by omega
  simpa only [he] using node_checks_3424 ⟨i.val-3424,by omega⟩
theorem output_checks_0 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (0+j.val)))=[⟨(0+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (0+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_32 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (32+j.val)))=[⟨(32+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (32+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_64 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (64+j.val)))=[⟨(64+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (64+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_96 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (96+j.val)))=[⟨(96+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (96+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_128 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (128+j.val)))=[⟨(128+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (128+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_160 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (160+j.val)))=[⟨(160+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (160+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_192 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (192+j.val)))=[⟨(192+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (192+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_224 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (224+j.val)))=[⟨(224+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (224+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_256 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (256+j.val)))=[⟨(256+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (256+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_288 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (288+j.val)))=[⟨(288+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (288+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_320 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (320+j.val)))=[⟨(320+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (320+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_352 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (352+j.val)))=[⟨(352+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (352+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_384 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (384+j.val)))=[⟨(384+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (384+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_416 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (416+j.val)))=[⟨(416+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (416+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_448 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (448+j.val)))=[⟨(448+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (448+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_480 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (480+j.val)))=[⟨(480+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (480+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_512 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (512+j.val)))=[⟨(512+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (512+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_544 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (544+j.val)))=[⟨(544+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (544+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_576 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (576+j.val)))=[⟨(576+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (576+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_608 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (608+j.val)))=[⟨(608+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (608+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_640 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (640+j.val)))=[⟨(640+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (640+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_672 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (672+j.val)))=[⟨(672+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (672+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_704 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (704+j.val)))=[⟨(704+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (704+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_736 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (736+j.val)))=[⟨(736+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (736+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_768 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (768+j.val)))=[⟨(768+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (768+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_800 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (800+j.val)))=[⟨(800+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (800+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_832 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (832+j.val)))=[⟨(832+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (832+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_864 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (864+j.val)))=[⟨(864+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (864+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_896 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (896+j.val)))=[⟨(896+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (896+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_928 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (928+j.val)))=[⟨(928+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (928+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_960 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (960+j.val)))=[⟨(960+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (960+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_992 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (992+j.val)))=[⟨(992+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (992+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_1024 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (1024+j.val)))=[⟨(1024+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (1024+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_1056 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (1056+j.val)))=[⟨(1056+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (1056+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_1088 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (1088+j.val)))=[⟨(1088+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (1088+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_1120 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (1120+j.val)))=[⟨(1120+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (1120+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_1152 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (1152+j.val)))=[⟨(1152+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (1152+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_1184 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (1184+j.val)))=[⟨(1184+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (1184+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_1216 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (1216+j.val)))=[⟨(1216+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (1216+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_1248 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (1248+j.val)))=[⟨(1248+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (1248+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_1280 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (1280+j.val)))=[⟨(1280+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (1280+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_1312 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (1312+j.val)))=[⟨(1312+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (1312+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_1344 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (1344+j.val)))=[⟨(1344+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (1344+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_1376 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (1376+j.val)))=[⟨(1376+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (1376+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_1408 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (1408+j.val)))=[⟨(1408+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (1408+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_1440 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (1440+j.val)))=[⟨(1440+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (1440+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_1472 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (1472+j.val)))=[⟨(1472+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (1472+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_1504 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (1504+j.val)))=[⟨(1504+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (1504+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_1536 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (1536+j.val)))=[⟨(1536+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (1536+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_1568 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (1568+j.val)))=[⟨(1568+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (1568+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_1600 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (1600+j.val)))=[⟨(1600+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (1600+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_1632 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (1632+j.val)))=[⟨(1632+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (1632+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_1664 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (1664+j.val)))=[⟨(1664+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (1664+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_1696 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (1696+j.val)))=[⟨(1696+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (1696+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_1728 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (1728+j.val)))=[⟨(1728+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (1728+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_1760 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (1760+j.val)))=[⟨(1760+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (1760+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_1792 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (1792+j.val)))=[⟨(1792+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (1792+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_1824 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (1824+j.val)))=[⟨(1824+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (1824+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_1856 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (1856+j.val)))=[⟨(1856+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (1856+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_1888 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (1888+j.val)))=[⟨(1888+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (1888+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_1920 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (1920+j.val)))=[⟨(1920+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (1920+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_1952 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (1952+j.val)))=[⟨(1952+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (1952+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_1984 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (1984+j.val)))=[⟨(1984+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (1984+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks_2016 : ∀ j : Fin 32,
    (normalize (gather rowAt (outputAt (2016+j.val)))=[⟨(2016+j.val),⟨1,0⟩,1⟩] ∧
      (outputAt (2016+j.val)).all (fun p => p.1<5495)=true) := by decide +kernel
theorem output_checks (i : Fin 2048) : (normalize (gather rowAt (outputAt i.val))=[⟨i.val,⟨1,0⟩,1⟩] ∧
      (outputAt i.val).all (fun p => p.1<5495)=true) := by
  by_cases h0 : i.val<32
  · have he : 0+(i.val-0)=i.val := by omega
    simpa only [he] using output_checks_0 ⟨i.val-0,by omega⟩
  by_cases h32 : i.val<64
  · have he : 32+(i.val-32)=i.val := by omega
    simpa only [he] using output_checks_32 ⟨i.val-32,by omega⟩
  by_cases h64 : i.val<96
  · have he : 64+(i.val-64)=i.val := by omega
    simpa only [he] using output_checks_64 ⟨i.val-64,by omega⟩
  by_cases h96 : i.val<128
  · have he : 96+(i.val-96)=i.val := by omega
    simpa only [he] using output_checks_96 ⟨i.val-96,by omega⟩
  by_cases h128 : i.val<160
  · have he : 128+(i.val-128)=i.val := by omega
    simpa only [he] using output_checks_128 ⟨i.val-128,by omega⟩
  by_cases h160 : i.val<192
  · have he : 160+(i.val-160)=i.val := by omega
    simpa only [he] using output_checks_160 ⟨i.val-160,by omega⟩
  by_cases h192 : i.val<224
  · have he : 192+(i.val-192)=i.val := by omega
    simpa only [he] using output_checks_192 ⟨i.val-192,by omega⟩
  by_cases h224 : i.val<256
  · have he : 224+(i.val-224)=i.val := by omega
    simpa only [he] using output_checks_224 ⟨i.val-224,by omega⟩
  by_cases h256 : i.val<288
  · have he : 256+(i.val-256)=i.val := by omega
    simpa only [he] using output_checks_256 ⟨i.val-256,by omega⟩
  by_cases h288 : i.val<320
  · have he : 288+(i.val-288)=i.val := by omega
    simpa only [he] using output_checks_288 ⟨i.val-288,by omega⟩
  by_cases h320 : i.val<352
  · have he : 320+(i.val-320)=i.val := by omega
    simpa only [he] using output_checks_320 ⟨i.val-320,by omega⟩
  by_cases h352 : i.val<384
  · have he : 352+(i.val-352)=i.val := by omega
    simpa only [he] using output_checks_352 ⟨i.val-352,by omega⟩
  by_cases h384 : i.val<416
  · have he : 384+(i.val-384)=i.val := by omega
    simpa only [he] using output_checks_384 ⟨i.val-384,by omega⟩
  by_cases h416 : i.val<448
  · have he : 416+(i.val-416)=i.val := by omega
    simpa only [he] using output_checks_416 ⟨i.val-416,by omega⟩
  by_cases h448 : i.val<480
  · have he : 448+(i.val-448)=i.val := by omega
    simpa only [he] using output_checks_448 ⟨i.val-448,by omega⟩
  by_cases h480 : i.val<512
  · have he : 480+(i.val-480)=i.val := by omega
    simpa only [he] using output_checks_480 ⟨i.val-480,by omega⟩
  by_cases h512 : i.val<544
  · have he : 512+(i.val-512)=i.val := by omega
    simpa only [he] using output_checks_512 ⟨i.val-512,by omega⟩
  by_cases h544 : i.val<576
  · have he : 544+(i.val-544)=i.val := by omega
    simpa only [he] using output_checks_544 ⟨i.val-544,by omega⟩
  by_cases h576 : i.val<608
  · have he : 576+(i.val-576)=i.val := by omega
    simpa only [he] using output_checks_576 ⟨i.val-576,by omega⟩
  by_cases h608 : i.val<640
  · have he : 608+(i.val-608)=i.val := by omega
    simpa only [he] using output_checks_608 ⟨i.val-608,by omega⟩
  by_cases h640 : i.val<672
  · have he : 640+(i.val-640)=i.val := by omega
    simpa only [he] using output_checks_640 ⟨i.val-640,by omega⟩
  by_cases h672 : i.val<704
  · have he : 672+(i.val-672)=i.val := by omega
    simpa only [he] using output_checks_672 ⟨i.val-672,by omega⟩
  by_cases h704 : i.val<736
  · have he : 704+(i.val-704)=i.val := by omega
    simpa only [he] using output_checks_704 ⟨i.val-704,by omega⟩
  by_cases h736 : i.val<768
  · have he : 736+(i.val-736)=i.val := by omega
    simpa only [he] using output_checks_736 ⟨i.val-736,by omega⟩
  by_cases h768 : i.val<800
  · have he : 768+(i.val-768)=i.val := by omega
    simpa only [he] using output_checks_768 ⟨i.val-768,by omega⟩
  by_cases h800 : i.val<832
  · have he : 800+(i.val-800)=i.val := by omega
    simpa only [he] using output_checks_800 ⟨i.val-800,by omega⟩
  by_cases h832 : i.val<864
  · have he : 832+(i.val-832)=i.val := by omega
    simpa only [he] using output_checks_832 ⟨i.val-832,by omega⟩
  by_cases h864 : i.val<896
  · have he : 864+(i.val-864)=i.val := by omega
    simpa only [he] using output_checks_864 ⟨i.val-864,by omega⟩
  by_cases h896 : i.val<928
  · have he : 896+(i.val-896)=i.val := by omega
    simpa only [he] using output_checks_896 ⟨i.val-896,by omega⟩
  by_cases h928 : i.val<960
  · have he : 928+(i.val-928)=i.val := by omega
    simpa only [he] using output_checks_928 ⟨i.val-928,by omega⟩
  by_cases h960 : i.val<992
  · have he : 960+(i.val-960)=i.val := by omega
    simpa only [he] using output_checks_960 ⟨i.val-960,by omega⟩
  by_cases h992 : i.val<1024
  · have he : 992+(i.val-992)=i.val := by omega
    simpa only [he] using output_checks_992 ⟨i.val-992,by omega⟩
  by_cases h1024 : i.val<1056
  · have he : 1024+(i.val-1024)=i.val := by omega
    simpa only [he] using output_checks_1024 ⟨i.val-1024,by omega⟩
  by_cases h1056 : i.val<1088
  · have he : 1056+(i.val-1056)=i.val := by omega
    simpa only [he] using output_checks_1056 ⟨i.val-1056,by omega⟩
  by_cases h1088 : i.val<1120
  · have he : 1088+(i.val-1088)=i.val := by omega
    simpa only [he] using output_checks_1088 ⟨i.val-1088,by omega⟩
  by_cases h1120 : i.val<1152
  · have he : 1120+(i.val-1120)=i.val := by omega
    simpa only [he] using output_checks_1120 ⟨i.val-1120,by omega⟩
  by_cases h1152 : i.val<1184
  · have he : 1152+(i.val-1152)=i.val := by omega
    simpa only [he] using output_checks_1152 ⟨i.val-1152,by omega⟩
  by_cases h1184 : i.val<1216
  · have he : 1184+(i.val-1184)=i.val := by omega
    simpa only [he] using output_checks_1184 ⟨i.val-1184,by omega⟩
  by_cases h1216 : i.val<1248
  · have he : 1216+(i.val-1216)=i.val := by omega
    simpa only [he] using output_checks_1216 ⟨i.val-1216,by omega⟩
  by_cases h1248 : i.val<1280
  · have he : 1248+(i.val-1248)=i.val := by omega
    simpa only [he] using output_checks_1248 ⟨i.val-1248,by omega⟩
  by_cases h1280 : i.val<1312
  · have he : 1280+(i.val-1280)=i.val := by omega
    simpa only [he] using output_checks_1280 ⟨i.val-1280,by omega⟩
  by_cases h1312 : i.val<1344
  · have he : 1312+(i.val-1312)=i.val := by omega
    simpa only [he] using output_checks_1312 ⟨i.val-1312,by omega⟩
  by_cases h1344 : i.val<1376
  · have he : 1344+(i.val-1344)=i.val := by omega
    simpa only [he] using output_checks_1344 ⟨i.val-1344,by omega⟩
  by_cases h1376 : i.val<1408
  · have he : 1376+(i.val-1376)=i.val := by omega
    simpa only [he] using output_checks_1376 ⟨i.val-1376,by omega⟩
  by_cases h1408 : i.val<1440
  · have he : 1408+(i.val-1408)=i.val := by omega
    simpa only [he] using output_checks_1408 ⟨i.val-1408,by omega⟩
  by_cases h1440 : i.val<1472
  · have he : 1440+(i.val-1440)=i.val := by omega
    simpa only [he] using output_checks_1440 ⟨i.val-1440,by omega⟩
  by_cases h1472 : i.val<1504
  · have he : 1472+(i.val-1472)=i.val := by omega
    simpa only [he] using output_checks_1472 ⟨i.val-1472,by omega⟩
  by_cases h1504 : i.val<1536
  · have he : 1504+(i.val-1504)=i.val := by omega
    simpa only [he] using output_checks_1504 ⟨i.val-1504,by omega⟩
  by_cases h1536 : i.val<1568
  · have he : 1536+(i.val-1536)=i.val := by omega
    simpa only [he] using output_checks_1536 ⟨i.val-1536,by omega⟩
  by_cases h1568 : i.val<1600
  · have he : 1568+(i.val-1568)=i.val := by omega
    simpa only [he] using output_checks_1568 ⟨i.val-1568,by omega⟩
  by_cases h1600 : i.val<1632
  · have he : 1600+(i.val-1600)=i.val := by omega
    simpa only [he] using output_checks_1600 ⟨i.val-1600,by omega⟩
  by_cases h1632 : i.val<1664
  · have he : 1632+(i.val-1632)=i.val := by omega
    simpa only [he] using output_checks_1632 ⟨i.val-1632,by omega⟩
  by_cases h1664 : i.val<1696
  · have he : 1664+(i.val-1664)=i.val := by omega
    simpa only [he] using output_checks_1664 ⟨i.val-1664,by omega⟩
  by_cases h1696 : i.val<1728
  · have he : 1696+(i.val-1696)=i.val := by omega
    simpa only [he] using output_checks_1696 ⟨i.val-1696,by omega⟩
  by_cases h1728 : i.val<1760
  · have he : 1728+(i.val-1728)=i.val := by omega
    simpa only [he] using output_checks_1728 ⟨i.val-1728,by omega⟩
  by_cases h1760 : i.val<1792
  · have he : 1760+(i.val-1760)=i.val := by omega
    simpa only [he] using output_checks_1760 ⟨i.val-1760,by omega⟩
  by_cases h1792 : i.val<1824
  · have he : 1792+(i.val-1792)=i.val := by omega
    simpa only [he] using output_checks_1792 ⟨i.val-1792,by omega⟩
  by_cases h1824 : i.val<1856
  · have he : 1824+(i.val-1824)=i.val := by omega
    simpa only [he] using output_checks_1824 ⟨i.val-1824,by omega⟩
  by_cases h1856 : i.val<1888
  · have he : 1856+(i.val-1856)=i.val := by omega
    simpa only [he] using output_checks_1856 ⟨i.val-1856,by omega⟩
  by_cases h1888 : i.val<1920
  · have he : 1888+(i.val-1888)=i.val := by omega
    simpa only [he] using output_checks_1888 ⟨i.val-1888,by omega⟩
  by_cases h1920 : i.val<1952
  · have he : 1920+(i.val-1920)=i.val := by omega
    simpa only [he] using output_checks_1920 ⟨i.val-1920,by omega⟩
  by_cases h1952 : i.val<1984
  · have he : 1952+(i.val-1952)=i.val := by omega
    simpa only [he] using output_checks_1952 ⟨i.val-1952,by omega⟩
  by_cases h1984 : i.val<2016
  · have he : 1984+(i.val-1984)=i.val := by omega
    simpa only [he] using output_checks_1984 ⟨i.val-1984,by omega⟩
  have he : 2016+(i.val-2016)=i.val := by omega
  simpa only [he] using output_checks_2016 ⟨i.val-2016,by omega⟩
end FourierSchur.OriginalProjectionNativeRowChecks
