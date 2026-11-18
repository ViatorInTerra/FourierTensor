import FourierTensor
import work_in_progress.BoundedKernelAxiomAudit

/-!
Check the all-length DFT contract, its exact operation count, its work
bound, the comparison with the published bound and the tensor subroutine.
-/

example : FourierTensor.CachedExecutor.exponent = 1 - 3 / 100000000 :=
  FourierTensor.CachedExecutor.exponent_eq

#check FourierTensor.AllLengthDFT.guarantee
#check FourierTensor.AllLengthDFT.running_time
#check FourierTensor.AllLengthDFT.count_from_length
#check FourierTensor.AllLengthDFT.time_le_allowance
#check FourierTensor.AllLengthDFT.time_bigO
#check FourierTensor.AllLengthDFT.every_length_bound
#check FourierTensor.AllLengthDFT.below_published_bound
#check FourierTensor.AllLengthDFT.below_nlogn
#check FourierTensor.AllLengthDFT.published_exponent_saving
#check FourierTensor.AllLengthDFT.upstream_lean_exponent_saving

#check FourierTensor.CachedExecutor.guarantee
#check FourierTensor.CachedExecutor.complete_executor
#check FourierTensor.CachedExecutor.local_rank32
#check FourierTensor.CachedExecutor.local_physical_rank32
#check FourierTensor.CachedExecutor.global_rank32
#check FourierTensor.CachedExecutor.all_outputs
#check FourierTensor.CachedExecutor.word_cost
#check FourierTensor.CachedExecutor.word_moment
#check FourierTensor.CachedExecutor.saving_ratio
#check FourierTensor.CachedExecutor.child_charge
#check FourierTensor.CachedExecutor.charged_allowance
#check FourierTensor.CenterCache.forward_all_centers
#check FourierTensor.CenterCache.inverse_all_centers
#check FourierTensor.CenterCacheRate.exact_rank_deficit
#check FourierTensor.CenterCacheRate.strict_padded_margin
#check FourierTensor.CenterCacheRate.original_padded_moment_gt_one
#check FourierTensor.CenterCacheRate.allowance_bound

#bounded_kernel_axioms FourierTensor.CachedExecutor.guarantee
#bounded_kernel_axioms FourierTensor.CachedExecutor.saving_ratio
#bounded_kernel_axioms FourierTensor.AllLengthDFT.guarantee
#bounded_kernel_axioms FourierTensor.AllLengthDFT.running_time
#bounded_kernel_axioms FourierTensor.AllLengthDFT.count_from_length
#bounded_kernel_axioms FourierTensor.AllLengthDFT.below_published_bound
