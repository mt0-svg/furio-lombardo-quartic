import FurioLombardo.M1.SieveBlocks

/-! Kernel check of the certificates of block 4 of the sieve (the rings above p = 19 and the characters of
the chosen conics at the listed points of C(F_19)). -/

namespace FurioLombardo.M1

set_option maxRecDepth 100000 in
theorem blockOK_4 : blockOK 4 = true := by decide +kernel

end FurioLombardo.M1
