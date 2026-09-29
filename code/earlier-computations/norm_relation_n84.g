# norm_relation_n84.g: group theory for S-units of the degree 84 field N (the quartic factor of the Prym's
# Weierstrass algebra over K21) through generalised norm relations (Etienne, arXiv 2411.13124; Biasse, Fieker,
# Hofmann, Page, arXiv 2002.12332).
# G = PGL(2,7) = Gal(M/Q), M the Galois closure of K21 (splitting field of the degree 8 polynomial of A3).
# For each conjugacy class of subgroups: order, index, number of real places of the fixed field (fixed points of
# complex conjugation c, an involution outside PSL(2,7), on the cosets), orbit sizes on P^1(F_7) (factor degrees
# of the degree 8 polynomial over the fixed field) and on G/D16 (factor degrees of the K21 polynomial).
# Then, for each irreducible character, the dimension of its fixed space under each subgroup.
# A generalised norm relation N_H = sum a_i N_{J_i} b_i over Q exists iff every irreducible rho with rho^H <> 0 has
# rho^{J_i} <> 0 for some i (Q[G] is a product of simple algebras; rational characters are used below).
# Run: gap -q norm_relation_n84.g
G := PGL(2,7);;   # permutation group on the 8 points of P^1(F_7)
Print("G order ", Size(G), ", degree ", NrMovedPoints(G), "\n");
S := DerivedSubgroup(G);;
inv := Filtered(List(ConjugacyClasses(G), Representative), g -> Order(g) = 2);;
c := First(inv, g -> not g in S);;
Print("complex conjugation: outer involution with ", 8 - NrMovedPoints(c), " fixed points on P^1(F_7)\n");
D16 := SylowSubgroup(G, 2);;
cls := ConjugacyClassesSubgroups(G);;
tbl := CharacterTable(G);; irr := Irr(tbl);;
fixdim := function(chi, H) return ScalarProduct(RestrictedClassFunction(chi, H), TrivialCharacter(H)); end;;
realpl := function(H) return Number(RightCosets(G, H), co -> co * c = co); end;;
orb := function(H, dom, act) return SortedList(List(Orbits(H, dom, act), Length)); end;;
cosD16 := RightCosets(G, D16);;
Print("\nirreducible character degrees: ", List(irr, x -> x[1]), "\n");
Print("class | order | index | real places | orbits on P1(F7) | orbits on G/D16 | in PSL | fixed dims of irr\n");
for k in [1..Length(cls)] do
  H := Representative(cls[k]);
  if Size(H) >= 2 and Size(H) < Size(G) then
    Print(k, " | ", Size(H), " | ", Index(G, H), " | ", realpl(H), " | ", orb(H, [1..8], OnPoints), " | ",
          orb(H, cosD16, OnRight), " | ", IsSubgroup(S, H), " | ", List(irr, x -> fixdim(x, H)), "\n");
  fi;
od;
# candidates for N: subgroups of order 4 contained in D16, not normal in D16, with core of order 2 in D16
Print("\ncandidates H for N (order 4, inside D16, core of order 2 in D16):\n");
cand := Filtered(Filtered(AllSubgroups(D16), H -> Size(H) = 4), H -> Size(Core(D16, H)) = 2);;
for H in cand do
  Print("  H = ", StructureDescription(H), ", class ", First([1..Length(cls)], k -> H in cls[k]), ", in PSL: ",
        IsSubgroup(S, H), ", real places ", realpl(H), ", orbits on P1 ", orb(H, [1..8], OnPoints),
        ", on G/D16 ", orb(H, cosD16, OnRight), "\n");
  Print("    irreducibles with rho^H <> 0 (degree, fixed dim): ",
        List(Filtered(irr, x -> fixdim(x, H) > 0), x -> [x[1], fixdim(x, H)]), "\n");
  Print("    unit rank of the fixed field: ", Length(Orbits(H, RightCosets(G, Group(c)), OnRight)) - 1, "\n");
od;
QUIT;
