# Step 1 of the 2-descent: the G_Q-module W0/Diag for the Galois set Omega of the 8 embeddings of A3.
# Gal(A3) is the transitive group of degree 8 and order 336 (two_descent_algebra.gp); here: it is 8T43,
# the permutation module F_2^Omega has composition factors 1, 6, 1, and W0/Diag (even weight vectors
# modulo the all-one vector) is absolutely irreducible with End = F_2.
# Run: gap -q two_descent_galois_module.g < /dev/null
Print("transitive groups of degree 8 and order 336: ", Filtered([1..NrTransitiveGroups(8)], i -> Size(TransitiveGroup(8,i)) = 336), "\n");
G := TransitiveGroup(8,43);
Print("8T43 = ", StructureDescription(G), ", order ", Size(G), "\n");
M := PermutationGModule(G, GF(2));
cf := MTX.CompositionFactors(M);
Print("composition factors of F_2^8: dims ", List(cf, m -> m.dimension), ", absolutely irreducible ", List(cf, m -> MTX.IsAbsolutelyIrreducible(m)), "\n");
one := function(b) if b then return One(GF(2)); else return Zero(GF(2)); fi; end;
gens := List(GeneratorsOfGroup(G), g -> PermutationMat(g, 8, GF(2)));
W0 := List([1..7], i -> List([1..8], j -> one((j = i) or (j = 8))));   # e_i + e_8
Dg := List([1..8], j -> One(GF(2)));                                   # all-one vector = sum of the seven e_i + e_8
B := W0{[1..6]};
full := Concatenation(B, [Dg]);
mats := List(gens, g -> List(B, b -> SolutionMat(full, b * g){[1..6]}));
Q := GModuleByMats(mats, GF(2));
Print("W0/Diag: dim ", Q.dimension, ", irreducible ", MTX.IsIrreducible(Q), ", absolutely irreducible ", MTX.IsAbsolutelyIrreducible(Q),
      ", dim End ", Length(MTX.BasisModuleEndomorphisms(Q)), "\n");
# no nonzero G-invariant element in W/Diag (so J(Q)[2] = 0)
Wd := List(Filtered(Tuples([0,1], 8), v -> v[8] = 0), v -> List(v, t -> one(t = 1)));  # representatives of W/Diag
fixed := Filtered(Wd, v -> ForAll(GeneratorsOfGroup(G), g -> (Permuted(v, g) = v) or (Permuted(v, g) = v + Dg)));
Print("G-invariant elements of W/Diag: ", Length(fixed), " (only 0)\n");
QUIT;
