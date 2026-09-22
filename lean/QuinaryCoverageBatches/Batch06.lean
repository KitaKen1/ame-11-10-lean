import MaskEncoding
import QuinaryCoverage
import QuinaryDirectBatches.Batch06

/-! Generated numeric mask check for batch 6. -/
namespace AMEProbe.QuinaryDirect.Batch06Coverage
open AMEProbe.QuinaryDirect
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

theorem mask_correct : ∀ r : Fin 256,
    (256 * 6 + r.val).bitIndices.length = 6 →
      mask (Batch06.lookup (256 * 6 + r.val)).val = 256 * 6 + r.val := by
  decide +kernel

end AMEProbe.QuinaryDirect.Batch06Coverage
#print axioms AMEProbe.QuinaryDirect.Batch06Coverage.mask_correct
