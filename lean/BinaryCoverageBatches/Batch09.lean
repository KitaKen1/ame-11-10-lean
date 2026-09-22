import MaskEncoding
import BinaryCoverage
import BinaryDirectBatches.Batch09

/-! Generated numeric mask check for batch 9. -/
namespace AMEProbe.BinaryDirect.Batch09Coverage
open AMEProbe.BinaryDirect
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

theorem mask_correct : ∀ r : Fin 256,
    (256 * 9 + r.val).bitIndices.length = 5 →
      mask (Batch09.lookup (256 * 9 + r.val)).val = 256 * 9 + r.val := by
  decide +kernel

end AMEProbe.BinaryDirect.Batch09Coverage
#print axioms AMEProbe.BinaryDirect.Batch09Coverage.mask_correct
