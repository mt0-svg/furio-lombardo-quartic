# galois_module_check.g: referee check of the Galois module J[2] = W0/Diag of the two-descent and of its local invariants.
# Written from scratch: GPG(2,7) is built from 2x2 matrices over GF(7) acting on the 8 points of P^1(F_7),
# the modules are built by hand, and the invariants are counted by brute force over all 2^8 vectors.
# Run: gap -q galois_module_check.g < /dev/null
F7 := GF(7);;
pts := Concatenation([[One(F7), Zero(F7)]], List(Elements(F7), t -> [t, One(F7)]));;   # P^1(F_7)
normal := function(v) if IsZero(v[2]) then return [One(F7), Zero(F7)]; else return v / v[2]; fi; end;;
act := function(m) return PermList(List(pts, p -> Position(pts, normal(p * m)))); end;;
GPG := Group(List(GeneratorsOfGroup(GL(2,7)), act));;
GPS := Group(List(GeneratorsOfGroup(SL(2,7)), act));;
Print("PGL(2,7) on P^1(F_7): order ", Size(GPG), ", transitive ", IsTransitive(GPG, [1..8]), "\n");
Print("PSL(2,7) on P^1(F_7): order ", Size(GPS), "\n");
t336 := Filtered([1..NrTransitiveGroups(8)], i -> Size(TransitiveGroup(8,i)) = 336);;
Print("transitive groups of degree 8 and order 336: ", t336, "; PGL(2,7) is 8T", TransitiveIdentification(GPG), "\n");

one := function(b) if b then return One(GF(2)); else return Zero(GF(2)); fi; end;;
V := List(Tuples([0,1], 8), v -> List(v, t -> one(t = 1)));;          # all of W = F_2^8
Om := List([1..8], i -> One(GF(2)));;
wt := v -> Number(v, t -> not IsZero(t));;
perm := function(v, g) return Permuted(v, g); end;;
# invariants of a subgroup H on W/Diag and on W0/Diag, counted by brute force
invWD := H -> Filtered(Filtered(V, v -> IsZero(v[8])), v -> ForAll(GeneratorsOfGroup(H), g -> perm(v,g) = v or perm(v,g) = v + Om));;
report := function(name, H)
  local I, Ieven;
  I := invWD(H);
  Ieven := Filtered(I, v -> wt(v) mod 2 = 0);
  Print(name, ": order ", Size(H), ", orbit sizes ", List(Orbits(H, [1..8]), Length),
        ", dim (W/Diag)^H = ", Log(Length(I), 2), ", dim (W0/Diag)^H = dim J[2]^H = ", Log(Length(Ieven), 2),
        ", odd orbit: ", ForAny(Orbits(H, [1..8]), o -> IsOddInt(Length(o))), "\n");
end;;

# module W0/Diag for G = GPG(2,7) and G = GPS(2,7)
heart := function(G)
  local B, full, mats;
  B := List([1..6], i -> List([1..8], j -> one(j = i or j = 8)));      # e_i + e_8, i = 1..6
  full := Concatenation(B, [Om]);                                     # plus Diag: a basis of W0
  mats := List(GeneratorsOfGroup(G), g -> List(B, b -> SolutionMat(full, perm(b, g)){[1..6]}));
  return GModuleByMats(mats, GF(2));
end;;
Mp := heart(GPG);; Ms := heart(GPS);;
Print("W0/Diag for PGL(2,7): irreducible ", MTX.IsIrreducible(Mp), ", absolutely irreducible ", MTX.IsAbsolutelyIrreducible(Mp),
      ", dim End ", Length(MTX.BasisModuleEndomorphisms(Mp)), "\n");
Print("control, W0/Diag for PSL(2,7): irreducible ", MTX.IsIrreducible(Ms), ", composition factor dims ",
      List(MTX.CompositionFactors(Ms), m -> m.dimension), "\n");
report("G = PGL(2,7)", GPG);
# check that the hyperplane argument of section 3 holds: the only G-invariant nonzero vector of W0 is Omega
Print("G-invariant nonzero vectors of W: ", Filtered(V, v -> not IsZero(v) and ForAll(GeneratorsOfGroup(GPG), g -> perm(v,g) = v)), "\n");

# all transitive subgroups of PGL(2,7) of 2-power index structure that could be a decomposition group at 2
Print("-- transitive subgroups of PGL(2,7) (up to conjugacy), with dim J[2]^H:\n");
for c in ConjugacyClassesSubgroups(GPG) do
  H := Representative(c);
  if IsTransitive(H, [1..8]) and IsSolvable(H) then
    report(Concatenation(StructureDescription(H), " (index in point stabilizer: stabilizer ", StructureDescription(Stabilizer(H, 1)), ")"), H);
  fi;
od;
# the groups with orbit structure 1 + 7 (possible decomposition groups at 7) and complex conjugation (2 fixed points)
Print("-- subgroups with an orbit of size 1 and one of size 7:\n");
for c in ConjugacyClassesSubgroups(GPG) do
  H := Representative(c);
  if SortedList(List(Orbits(H, [1..8]), Length)) = [1, 7] then report(StructureDescription(H), H); fi;
od;
Print("-- involutions of PGL(2,7) by number of fixed points, with dim J[2]^<c>:\n");
for c in ConjugacyClasses(GPG) do
  g := Representative(c);
  if Order(g) = 2 then report(Concatenation("involution with ", String(8 - NrMovedPoints(g)), " fixed points"), Group(g)); fi;
od;
QUIT;
