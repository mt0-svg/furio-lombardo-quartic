import FurioLombardo.M1.SieveBlocks

/-! Kernel check of the certificates of block 1 of the sieve (the rings above p = 11 and the characters of
the chosen conics at the listed points of C(F_11)). -/

namespace FurioLombardo.M1

set_option maxRecDepth 100000 in
theorem blockOK_1 : blockOK 1 = true := by decide +kernel

end FurioLombardo.M1
