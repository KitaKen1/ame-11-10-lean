import MaskEncoding
import BinaryCoverage
import BinaryDirectBatches.Batch08

/-! Generated numeric mask check for batch 8. -/
namespace AMEProbe.BinaryDirect.Batch08Coverage
open AMEProbe.BinaryDirect
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

theorem mask_correct : ∀ r : Fin 256,
    (256 * 8 + r.val).bitIndices.length = 5 →
      mask (Batch08.lookup (256 * 8 + r.val)).val = 256 * 8 + r.val := by
  decide +kernel

end AMEProbe.BinaryDirect.Batch08Coverage
#print axioms AMEProbe.BinaryDirect.Batch08Coverage.mask_correct
