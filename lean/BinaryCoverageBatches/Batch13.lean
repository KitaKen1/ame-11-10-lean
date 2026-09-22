import MaskEncoding
import BinaryCoverage
import BinaryDirectBatches.Batch13

/-! Generated numeric mask check for batch 13. -/
namespace AMEProbe.BinaryDirect.Batch13Coverage
open AMEProbe.BinaryDirect
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

theorem mask_correct : ∀ r : Fin 256,
    (256 * 13 + r.val).bitIndices.length = 5 →
      mask (Batch13.lookup (256 * 13 + r.val)).val = 256 * 13 + r.val := by
  decide +kernel

end AMEProbe.BinaryDirect.Batch13Coverage
#print axioms AMEProbe.BinaryDirect.Batch13Coverage.mask_correct
