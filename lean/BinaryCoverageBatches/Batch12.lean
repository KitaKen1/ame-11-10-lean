import MaskEncoding
import BinaryCoverage
import BinaryDirectBatches.Batch12

/-! Generated numeric mask check for batch 12. -/
namespace AMEProbe.BinaryDirect.Batch12Coverage
open AMEProbe.BinaryDirect
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

theorem mask_correct : ∀ r : Fin 256,
    (256 * 12 + r.val).bitIndices.length = 5 →
      mask (Batch12.lookup (256 * 12 + r.val)).val = 256 * 12 + r.val := by
  decide +kernel

end AMEProbe.BinaryDirect.Batch12Coverage
#print axioms AMEProbe.BinaryDirect.Batch12Coverage.mask_correct
