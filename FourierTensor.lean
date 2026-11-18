import FourierSchur.Executor
import FourierTensor.AllLengthDFT

/-!
The public import exposes the exact DFT and its tensor backend through
`FourierTensor.AllLengthDFT.guarantee` and
`FourierTensor.CachedExecutor.guarantee`. It also includes the earlier
99-call tensor executor, `FourierSchur.Executor.guarantee`.
-/
