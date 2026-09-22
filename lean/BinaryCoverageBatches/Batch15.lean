import MaskEncoding
import BinaryCoverage
import BinaryDirectBatches.Batch15

/-! Generated numeric mask check for batch 15. -/
namespace AMEProbe.BinaryDirect.Batch15Coverage
open AMEProbe.BinaryDirect
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

theorem mask_correct : ∀ r : Fin 256,
    (256 * 15 + r.val).bitIndices.length = 5 →
      mask (Batch15.lookup (256 * 15 + r.val)).val = 256 * 15 + r.val := by
  decide +kernel

end AMEProbe.BinaryDirect.Batch15Coverage
#print axioms AMEProbe.BinaryDirect.Batch15Coverage.mask_correct
