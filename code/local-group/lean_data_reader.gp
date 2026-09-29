\\ lean_data_reader.gp: read the data lists of the Lean files (so the certificates use exactly the Lean data).
\\ leandef(file, name): the value of `def name ... := <list>` (the list literal up to the next blank line).
leandef(file, name) = {
  my(L = readstr(file), i0 = 0, s);
  for (i = 1, #L, my(w = strsplit(L[i], " ")); if (#w >= 2 && w[1] == "def" && w[2] == name, i0 = i; break));
  if (i0 == 0, error("leandef: no def ", name));
  s = strsplit(L[i0], ":=")[2];
  for (i = i0 + 1, #L, if (L[i] == "", break); s = Str(s, L[i]));
  eval(s);
}
LDIR = "../../FurioLombardo/Discharge/M3a/";
LB = Str(LDIR, "DataBruin.lean"); LL = Str(LDIR, "LocalData.lean");
FnDataL = leandef(LB, "FnData"); qDenL = leandef(LB, "qDen"); hDenL = leandef(LB, "hDen"); qDataL = leandef(LB, "qData");
hDataL = leandef(LB, "hData"); dnDataL = leandef(LB, "dnData"); dDataL = leandef(LB, "dData");
abDataL = leandef(LL, "abData"); maDenL = leandef(LL, "maDen"); mbDenL = leandef(LL, "mbDen");
