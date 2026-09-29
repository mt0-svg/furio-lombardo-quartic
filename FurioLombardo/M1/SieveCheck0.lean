import FurioLombardo.M1.SieveBlocks

/-! Kernel check of the certificates of block 0 of the sieve (the rings above p = 5 and the characters of
the chosen conics at the listed points of C(F_5)). -/

namespace FurioLombardo.M1

set_option maxRecDepth 100000 in
theorem blockOK_0 : blockOK 0 = true := by decide +kernel

end FurioLombardo.M1
