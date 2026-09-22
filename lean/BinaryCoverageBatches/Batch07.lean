import MaskEncoding
import BinaryCoverage
import BinaryDirectBatches.Batch07

/-! Generated numeric mask check for batch 7. -/
namespace AMEProbe.BinaryDirect.Batch07Coverage
open AMEProbe.BinaryDirect
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

theorem mask_correct : ∀ r : Fin 256,
    (256 * 7 + r.val).bitIndices.length = 5 →
      mask (Batch07.lookup (256 * 7 + r.val)).val = 256 * 7 + r.val := by
  decide +kernel

end AMEProbe.BinaryDirect.Batch07Coverage
#print axioms AMEProbe.BinaryDirect.Batch07Coverage.mask_correct
