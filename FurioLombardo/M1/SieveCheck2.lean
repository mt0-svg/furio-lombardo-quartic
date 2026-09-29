import FurioLombardo.M1.SieveBlocks

/-! Kernel check of the certificates of block 2 of the sieve (the rings above p = 13 and the characters of
the chosen conics at the listed points of C(F_13)). -/

namespace FurioLombardo.M1

set_option maxRecDepth 100000 in
theorem blockOK_2 : blockOK 2 = true := by decide +kernel

end FurioLombardo.M1
