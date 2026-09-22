import MaskEncoding
import QuinaryCoverage
import QuinaryDirectBatches.Batch05

/-! Generated numeric mask check for batch 5. -/
namespace AMEProbe.QuinaryDirect.Batch05Coverage
open AMEProbe.QuinaryDirect
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

theorem mask_correct : ∀ r : Fin 256,
    (256 * 5 + r.val).bitIndices.length = 6 →
      mask (Batch05.lookup (256 * 5 + r.val)).val = 256 * 5 + r.val := by
  decide +kernel

end AMEProbe.QuinaryDirect.Batch05Coverage
#print axioms AMEProbe.QuinaryDirect.Batch05Coverage.mask_correct
