import FurioLombardo.M1.SieveBlocks

/-! Kernel check of the certificates of block 3 of the sieve (the rings above p = 17 and the characters of
the chosen conics at the listed points of C(F_17)). -/

namespace FurioLombardo.M1

set_option maxRecDepth 100000 in
theorem blockOK_3 : blockOK 3 = true := by decide +kernel

end FurioLombardo.M1
