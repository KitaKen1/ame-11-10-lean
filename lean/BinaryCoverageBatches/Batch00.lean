import MaskEncoding
import BinaryCoverage
import BinaryDirectBatches.Batch00

/-! Generated numeric mask check for batch 0. -/
namespace AMEProbe.BinaryDirect.Batch00Coverage
open AMEProbe.BinaryDirect
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

theorem mask_correct : ∀ r : Fin 256,
    (256 * 0 + r.val).bitIndices.length = 5 →
      mask (Batch00.lookup (256 * 0 + r.val)).val = 256 * 0 + r.val := by
  decide +kernel

end AMEProbe.BinaryDirect.Batch00Coverage
#print axioms AMEProbe.BinaryDirect.Batch00Coverage.mask_correct
