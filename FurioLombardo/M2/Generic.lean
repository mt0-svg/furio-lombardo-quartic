import FurioLombardo.M2.DataAll
import FurioLombardo.M2.Cover
import FurioLombardo.M2.Sound

/-!
# Every non-special prime up to `Bnd` (lane M2)

The 120 kernel-checked blocks `FurioLombardo.M2.Data.P000` to `P119` cover `[0, 120001)`; with
`cover_sound` and `checkPrime_sound`, every prime ideal above a prime `p ≤ Bnd`, `p ∉ {2, 7, 45613}`,
with `p ^ f(P) ≤ Bnd` is principal.
-/

namespace FurioLombardo.M2

open NumberField Ideal

theorem generic_record (p : ℕ) (hp : p.Prime) (hpB : p ≤ Bnd) (hs : isSpecial p = false) :
    ∃ N, checkPrime p N = true := by
  have hpB' : p ≤ 120000 := hpB
  by_cases h000 : p < 1000
  · exact cover_sound 0 1000 Data.recsP000 Data.covP000 Data.okP000 p hp (by omega) (by omega) hs
  by_cases h001 : p < 2000
  · exact cover_sound 1000 1000 Data.recsP001 Data.covP001 Data.okP001 p hp (by omega) (by omega) hs
  by_cases h002 : p < 3000
  · exact cover_sound 2000 1000 Data.recsP002 Data.covP002 Data.okP002 p hp (by omega) (by omega) hs
  by_cases h003 : p < 4000
  · exact cover_sound 3000 1000 Data.recsP003 Data.covP003 Data.okP003 p hp (by omega) (by omega) hs
  by_cases h004 : p < 5000
  · exact cover_sound 4000 1000 Data.recsP004 Data.covP004 Data.okP004 p hp (by omega) (by omega) hs
  by_cases h005 : p < 6000
  · exact cover_sound 5000 1000 Data.recsP005 Data.covP005 Data.okP005 p hp (by omega) (by omega) hs
  by_cases h006 : p < 7000
  · exact cover_sound 6000 1000 Data.recsP006 Data.covP006 Data.okP006 p hp (by omega) (by omega) hs
  by_cases h007 : p < 8000
  · exact cover_sound 7000 1000 Data.recsP007 Data.covP007 Data.okP007 p hp (by omega) (by omega) hs
  by_cases h008 : p < 9000
  · exact cover_sound 8000 1000 Data.recsP008 Data.covP008 Data.okP008 p hp (by omega) (by omega) hs
  by_cases h009 : p < 10000
  · exact cover_sound 9000 1000 Data.recsP009 Data.covP009 Data.okP009 p hp (by omega) (by omega) hs
  by_cases h010 : p < 11000
  · exact cover_sound 10000 1000 Data.recsP010 Data.covP010 Data.okP010 p hp (by omega) (by omega) hs
  by_cases h011 : p < 12000
  · exact cover_sound 11000 1000 Data.recsP011 Data.covP011 Data.okP011 p hp (by omega) (by omega) hs
  by_cases h012 : p < 13000
  · exact cover_sound 12000 1000 Data.recsP012 Data.covP012 Data.okP012 p hp (by omega) (by omega) hs
  by_cases h013 : p < 14000
  · exact cover_sound 13000 1000 Data.recsP013 Data.covP013 Data.okP013 p hp (by omega) (by omega) hs
  by_cases h014 : p < 15000
  · exact cover_sound 14000 1000 Data.recsP014 Data.covP014 Data.okP014 p hp (by omega) (by omega) hs
  by_cases h015 : p < 16000
  · exact cover_sound 15000 1000 Data.recsP015 Data.covP015 Data.okP015 p hp (by omega) (by omega) hs
  by_cases h016 : p < 17000
  · exact cover_sound 16000 1000 Data.recsP016 Data.covP016 Data.okP016 p hp (by omega) (by omega) hs
  by_cases h017 : p < 18000
  · exact cover_sound 17000 1000 Data.recsP017 Data.covP017 Data.okP017 p hp (by omega) (by omega) hs
  by_cases h018 : p < 19000
  · exact cover_sound 18000 1000 Data.recsP018 Data.covP018 Data.okP018 p hp (by omega) (by omega) hs
  by_cases h019 : p < 20000
  · exact cover_sound 19000 1000 Data.recsP019 Data.covP019 Data.okP019 p hp (by omega) (by omega) hs
  by_cases h020 : p < 21000
  · exact cover_sound 20000 1000 Data.recsP020 Data.covP020 Data.okP020 p hp (by omega) (by omega) hs
  by_cases h021 : p < 22000
  · exact cover_sound 21000 1000 Data.recsP021 Data.covP021 Data.okP021 p hp (by omega) (by omega) hs
  by_cases h022 : p < 23000
  · exact cover_sound 22000 1000 Data.recsP022 Data.covP022 Data.okP022 p hp (by omega) (by omega) hs
  by_cases h023 : p < 24000
  · exact cover_sound 23000 1000 Data.recsP023 Data.covP023 Data.okP023 p hp (by omega) (by omega) hs
  by_cases h024 : p < 25000
  · exact cover_sound 24000 1000 Data.recsP024 Data.covP024 Data.okP024 p hp (by omega) (by omega) hs
  by_cases h025 : p < 26000
  · exact cover_sound 25000 1000 Data.recsP025 Data.covP025 Data.okP025 p hp (by omega) (by omega) hs
  by_cases h026 : p < 27000
  · exact cover_sound 26000 1000 Data.recsP026 Data.covP026 Data.okP026 p hp (by omega) (by omega) hs
  by_cases h027 : p < 28000
  · exact cover_sound 27000 1000 Data.recsP027 Data.covP027 Data.okP027 p hp (by omega) (by omega) hs
  by_cases h028 : p < 29000
  · exact cover_sound 28000 1000 Data.recsP028 Data.covP028 Data.okP028 p hp (by omega) (by omega) hs
  by_cases h029 : p < 30000
  · exact cover_sound 29000 1000 Data.recsP029 Data.covP029 Data.okP029 p hp (by omega) (by omega) hs
  by_cases h030 : p < 31000
  · exact cover_sound 30000 1000 Data.recsP030 Data.covP030 Data.okP030 p hp (by omega) (by omega) hs
  by_cases h031 : p < 32000
  · exact cover_sound 31000 1000 Data.recsP031 Data.covP031 Data.okP031 p hp (by omega) (by omega) hs
  by_cases h032 : p < 33000
  · exact cover_sound 32000 1000 Data.recsP032 Data.covP032 Data.okP032 p hp (by omega) (by omega) hs
  by_cases h033 : p < 34000
  · exact cover_sound 33000 1000 Data.recsP033 Data.covP033 Data.okP033 p hp (by omega) (by omega) hs
  by_cases h034 : p < 35000
  · exact cover_sound 34000 1000 Data.recsP034 Data.covP034 Data.okP034 p hp (by omega) (by omega) hs
  by_cases h035 : p < 36000
  · exact cover_sound 35000 1000 Data.recsP035 Data.covP035 Data.okP035 p hp (by omega) (by omega) hs
  by_cases h036 : p < 37000
  · exact cover_sound 36000 1000 Data.recsP036 Data.covP036 Data.okP036 p hp (by omega) (by omega) hs
  by_cases h037 : p < 38000
  · exact cover_sound 37000 1000 Data.recsP037 Data.covP037 Data.okP037 p hp (by omega) (by omega) hs
  by_cases h038 : p < 39000
  · exact cover_sound 38000 1000 Data.recsP038 Data.covP038 Data.okP038 p hp (by omega) (by omega) hs
  by_cases h039 : p < 40000
  · exact cover_sound 39000 1000 Data.recsP039 Data.covP039 Data.okP039 p hp (by omega) (by omega) hs
  by_cases h040 : p < 41000
  · exact cover_sound 40000 1000 Data.recsP040 Data.covP040 Data.okP040 p hp (by omega) (by omega) hs
  by_cases h041 : p < 42000
  · exact cover_sound 41000 1000 Data.recsP041 Data.covP041 Data.okP041 p hp (by omega) (by omega) hs
  by_cases h042 : p < 43000
  · exact cover_sound 42000 1000 Data.recsP042 Data.covP042 Data.okP042 p hp (by omega) (by omega) hs
  by_cases h043 : p < 44000
  · exact cover_sound 43000 1000 Data.recsP043 Data.covP043 Data.okP043 p hp (by omega) (by omega) hs
  by_cases h044 : p < 45000
  · exact cover_sound 44000 1000 Data.recsP044 Data.covP044 Data.okP044 p hp (by omega) (by omega) hs
  by_cases h045 : p < 46000
  · exact cover_sound 45000 1000 Data.recsP045 Data.covP045 Data.okP045 p hp (by omega) (by omega) hs
  by_cases h046 : p < 47000
  · exact cover_sound 46000 1000 Data.recsP046 Data.covP046 Data.okP046 p hp (by omega) (by omega) hs
  by_cases h047 : p < 48000
  · exact cover_sound 47000 1000 Data.recsP047 Data.covP047 Data.okP047 p hp (by omega) (by omega) hs
  by_cases h048 : p < 49000
  · exact cover_sound 48000 1000 Data.recsP048 Data.covP048 Data.okP048 p hp (by omega) (by omega) hs
  by_cases h049 : p < 50000
  · exact cover_sound 49000 1000 Data.recsP049 Data.covP049 Data.okP049 p hp (by omega) (by omega) hs
  by_cases h050 : p < 51000
  · exact cover_sound 50000 1000 Data.recsP050 Data.covP050 Data.okP050 p hp (by omega) (by omega) hs
  by_cases h051 : p < 52000
  · exact cover_sound 51000 1000 Data.recsP051 Data.covP051 Data.okP051 p hp (by omega) (by omega) hs
  by_cases h052 : p < 53000
  · exact cover_sound 52000 1000 Data.recsP052 Data.covP052 Data.okP052 p hp (by omega) (by omega) hs
  by_cases h053 : p < 54000
  · exact cover_sound 53000 1000 Data.recsP053 Data.covP053 Data.okP053 p hp (by omega) (by omega) hs
  by_cases h054 : p < 55000
  · exact cover_sound 54000 1000 Data.recsP054 Data.covP054 Data.okP054 p hp (by omega) (by omega) hs
  by_cases h055 : p < 56000
  · exact cover_sound 55000 1000 Data.recsP055 Data.covP055 Data.okP055 p hp (by omega) (by omega) hs
  by_cases h056 : p < 57000
  · exact cover_sound 56000 1000 Data.recsP056 Data.covP056 Data.okP056 p hp (by omega) (by omega) hs
  by_cases h057 : p < 58000
  · exact cover_sound 57000 1000 Data.recsP057 Data.covP057 Data.okP057 p hp (by omega) (by omega) hs
  by_cases h058 : p < 59000
  · exact cover_sound 58000 1000 Data.recsP058 Data.covP058 Data.okP058 p hp (by omega) (by omega) hs
  by_cases h059 : p < 60000
  · exact cover_sound 59000 1000 Data.recsP059 Data.covP059 Data.okP059 p hp (by omega) (by omega) hs
  by_cases h060 : p < 61000
  · exact cover_sound 60000 1000 Data.recsP060 Data.covP060 Data.okP060 p hp (by omega) (by omega) hs
  by_cases h061 : p < 62000
  · exact cover_sound 61000 1000 Data.recsP061 Data.covP061 Data.okP061 p hp (by omega) (by omega) hs
  by_cases h062 : p < 63000
  · exact cover_sound 62000 1000 Data.recsP062 Data.covP062 Data.okP062 p hp (by omega) (by omega) hs
  by_cases h063 : p < 64000
  · exact cover_sound 63000 1000 Data.recsP063 Data.covP063 Data.okP063 p hp (by omega) (by omega) hs
  by_cases h064 : p < 65000
  · exact cover_sound 64000 1000 Data.recsP064 Data.covP064 Data.okP064 p hp (by omega) (by omega) hs
  by_cases h065 : p < 66000
  · exact cover_sound 65000 1000 Data.recsP065 Data.covP065 Data.okP065 p hp (by omega) (by omega) hs
  by_cases h066 : p < 67000
  · exact cover_sound 66000 1000 Data.recsP066 Data.covP066 Data.okP066 p hp (by omega) (by omega) hs
  by_cases h067 : p < 68000
  · exact cover_sound 67000 1000 Data.recsP067 Data.covP067 Data.okP067 p hp (by omega) (by omega) hs
  by_cases h068 : p < 69000
  · exact cover_sound 68000 1000 Data.recsP068 Data.covP068 Data.okP068 p hp (by omega) (by omega) hs
  by_cases h069 : p < 70000
  · exact cover_sound 69000 1000 Data.recsP069 Data.covP069 Data.okP069 p hp (by omega) (by omega) hs
  by_cases h070 : p < 71000
  · exact cover_sound 70000 1000 Data.recsP070 Data.covP070 Data.okP070 p hp (by omega) (by omega) hs
  by_cases h071 : p < 72000
  · exact cover_sound 71000 1000 Data.recsP071 Data.covP071 Data.okP071 p hp (by omega) (by omega) hs
  by_cases h072 : p < 73000
  · exact cover_sound 72000 1000 Data.recsP072 Data.covP072 Data.okP072 p hp (by omega) (by omega) hs
  by_cases h073 : p < 74000
  · exact cover_sound 73000 1000 Data.recsP073 Data.covP073 Data.okP073 p hp (by omega) (by omega) hs
  by_cases h074 : p < 75000
  · exact cover_sound 74000 1000 Data.recsP074 Data.covP074 Data.okP074 p hp (by omega) (by omega) hs
  by_cases h075 : p < 76000
  · exact cover_sound 75000 1000 Data.recsP075 Data.covP075 Data.okP075 p hp (by omega) (by omega) hs
  by_cases h076 : p < 77000
  · exact cover_sound 76000 1000 Data.recsP076 Data.covP076 Data.okP076 p hp (by omega) (by omega) hs
  by_cases h077 : p < 78000
  · exact cover_sound 77000 1000 Data.recsP077 Data.covP077 Data.okP077 p hp (by omega) (by omega) hs
  by_cases h078 : p < 79000
  · exact cover_sound 78000 1000 Data.recsP078 Data.covP078 Data.okP078 p hp (by omega) (by omega) hs
  by_cases h079 : p < 80000
  · exact cover_sound 79000 1000 Data.recsP079 Data.covP079 Data.okP079 p hp (by omega) (by omega) hs
  by_cases h080 : p < 81000
  · exact cover_sound 80000 1000 Data.recsP080 Data.covP080 Data.okP080 p hp (by omega) (by omega) hs
  by_cases h081 : p < 82000
  · exact cover_sound 81000 1000 Data.recsP081 Data.covP081 Data.okP081 p hp (by omega) (by omega) hs
  by_cases h082 : p < 83000
  · exact cover_sound 82000 1000 Data.recsP082 Data.covP082 Data.okP082 p hp (by omega) (by omega) hs
  by_cases h083 : p < 84000
  · exact cover_sound 83000 1000 Data.recsP083 Data.covP083 Data.okP083 p hp (by omega) (by omega) hs
  by_cases h084 : p < 85000
  · exact cover_sound 84000 1000 Data.recsP084 Data.covP084 Data.okP084 p hp (by omega) (by omega) hs
  by_cases h085 : p < 86000
  · exact cover_sound 85000 1000 Data.recsP085 Data.covP085 Data.okP085 p hp (by omega) (by omega) hs
  by_cases h086 : p < 87000
  · exact cover_sound 86000 1000 Data.recsP086 Data.covP086 Data.okP086 p hp (by omega) (by omega) hs
  by_cases h087 : p < 88000
  · exact cover_sound 87000 1000 Data.recsP087 Data.covP087 Data.okP087 p hp (by omega) (by omega) hs
  by_cases h088 : p < 89000
  · exact cover_sound 88000 1000 Data.recsP088 Data.covP088 Data.okP088 p hp (by omega) (by omega) hs
  by_cases h089 : p < 90000
  · exact cover_sound 89000 1000 Data.recsP089 Data.covP089 Data.okP089 p hp (by omega) (by omega) hs
  by_cases h090 : p < 91000
  · exact cover_sound 90000 1000 Data.recsP090 Data.covP090 Data.okP090 p hp (by omega) (by omega) hs
  by_cases h091 : p < 92000
  · exact cover_sound 91000 1000 Data.recsP091 Data.covP091 Data.okP091 p hp (by omega) (by omega) hs
  by_cases h092 : p < 93000
  · exact cover_sound 92000 1000 Data.recsP092 Data.covP092 Data.okP092 p hp (by omega) (by omega) hs
  by_cases h093 : p < 94000
  · exact cover_sound 93000 1000 Data.recsP093 Data.covP093 Data.okP093 p hp (by omega) (by omega) hs
  by_cases h094 : p < 95000
  · exact cover_sound 94000 1000 Data.recsP094 Data.covP094 Data.okP094 p hp (by omega) (by omega) hs
  by_cases h095 : p < 96000
  · exact cover_sound 95000 1000 Data.recsP095 Data.covP095 Data.okP095 p hp (by omega) (by omega) hs
  by_cases h096 : p < 97000
  · exact cover_sound 96000 1000 Data.recsP096 Data.covP096 Data.okP096 p hp (by omega) (by omega) hs
  by_cases h097 : p < 98000
  · exact cover_sound 97000 1000 Data.recsP097 Data.covP097 Data.okP097 p hp (by omega) (by omega) hs
  by_cases h098 : p < 99000
  · exact cover_sound 98000 1000 Data.recsP098 Data.covP098 Data.okP098 p hp (by omega) (by omega) hs
  by_cases h099 : p < 100000
  · exact cover_sound 99000 1000 Data.recsP099 Data.covP099 Data.okP099 p hp (by omega) (by omega) hs
  by_cases h100 : p < 101000
  · exact cover_sound 100000 1000 Data.recsP100 Data.covP100 Data.okP100 p hp (by omega) (by omega) hs
  by_cases h101 : p < 102000
  · exact cover_sound 101000 1000 Data.recsP101 Data.covP101 Data.okP101 p hp (by omega) (by omega) hs
  by_cases h102 : p < 103000
  · exact cover_sound 102000 1000 Data.recsP102 Data.covP102 Data.okP102 p hp (by omega) (by omega) hs
  by_cases h103 : p < 104000
  · exact cover_sound 103000 1000 Data.recsP103 Data.covP103 Data.okP103 p hp (by omega) (by omega) hs
  by_cases h104 : p < 105000
  · exact cover_sound 104000 1000 Data.recsP104 Data.covP104 Data.okP104 p hp (by omega) (by omega) hs
  by_cases h105 : p < 106000
  · exact cover_sound 105000 1000 Data.recsP105 Data.covP105 Data.okP105 p hp (by omega) (by omega) hs
  by_cases h106 : p < 107000
  · exact cover_sound 106000 1000 Data.recsP106 Data.covP106 Data.okP106 p hp (by omega) (by omega) hs
  by_cases h107 : p < 108000
  · exact cover_sound 107000 1000 Data.recsP107 Data.covP107 Data.okP107 p hp (by omega) (by omega) hs
  by_cases h108 : p < 109000
  · exact cover_sound 108000 1000 Data.recsP108 Data.covP108 Data.okP108 p hp (by omega) (by omega) hs
  by_cases h109 : p < 110000
  · exact cover_sound 109000 1000 Data.recsP109 Data.covP109 Data.okP109 p hp (by omega) (by omega) hs
  by_cases h110 : p < 111000
  · exact cover_sound 110000 1000 Data.recsP110 Data.covP110 Data.okP110 p hp (by omega) (by omega) hs
  by_cases h111 : p < 112000
  · exact cover_sound 111000 1000 Data.recsP111 Data.covP111 Data.okP111 p hp (by omega) (by omega) hs
  by_cases h112 : p < 113000
  · exact cover_sound 112000 1000 Data.recsP112 Data.covP112 Data.okP112 p hp (by omega) (by omega) hs
  by_cases h113 : p < 114000
  · exact cover_sound 113000 1000 Data.recsP113 Data.covP113 Data.okP113 p hp (by omega) (by omega) hs
  by_cases h114 : p < 115000
  · exact cover_sound 114000 1000 Data.recsP114 Data.covP114 Data.okP114 p hp (by omega) (by omega) hs
  by_cases h115 : p < 116000
  · exact cover_sound 115000 1000 Data.recsP115 Data.covP115 Data.okP115 p hp (by omega) (by omega) hs
  by_cases h116 : p < 117000
  · exact cover_sound 116000 1000 Data.recsP116 Data.covP116 Data.okP116 p hp (by omega) (by omega) hs
  by_cases h117 : p < 118000
  · exact cover_sound 117000 1000 Data.recsP117 Data.covP117 Data.okP117 p hp (by omega) (by omega) hs
  by_cases h118 : p < 119000
  · exact cover_sound 118000 1000 Data.recsP118 Data.covP118 Data.okP118 p hp (by omega) (by omega) hs
  exact cover_sound 119000 1001 Data.recsP119 Data.covP119 Data.okP119 p hp (by omega) (by omega) hs

theorem generic_prime (p : ℕ) (hp : p.Prime) (hpB : p ≤ Bnd) (hs : isSpecial p = false)
    (P : Ideal (𝓞 K21)) (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K21))
    (hPB : p ^ P.inertiaDeg ℤ ≤ Bnd) : Submodule.IsPrincipal P := by
  obtain ⟨N, hN⟩ := generic_record p hp hpB hs
  exact checkPrime_sound p N hp hN P hP hPB

end FurioLombardo.M2
