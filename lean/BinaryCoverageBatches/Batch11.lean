import MaskEncoding
import BinaryCoverage
import BinaryDirectBatches.Batch11

/-! Generated numeric mask check for batch 11. -/
namespace AMEProbe.BinaryDirect.Batch11Coverage
open AMEProbe.BinaryDirect
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

theorem mask_correct : ∀ r : Fin 256,
    (256 * 11 + r.val).bitIndices.length = 5 →
      mask (Batch11.lookup (256 * 11 + r.val)).val = 256 * 11 + r.val := by
  decide +kernel

end AMEProbe.BinaryDirect.Batch11Coverage
#print axioms AMEProbe.BinaryDirect.Batch11Coverage.mask_correct
