\\ selmer_dim_subsets.gp: dimension of X_P = {x in A(S,2) : res_w(x) in W_w for w in P} for every subset P of the seven
\\ places of S and infinity (data selmer_injectivity_places_twist<k>.bin of selmer_injectivity_places.gp). dim X = 19 (dim Sel = 4) for P = all.
\\ Lists the minimal subsets P with dim X_P = 19.
\\ Run: gp -q selmer_dim_subsets.gp
default(parisizemax, 10^9); default(nbthreads, 1);
f2annih(W, n) = { if (#W == 0, return(matid(n))); my(Kr = lift(matker(Mod(W~, 2)))); if (#Kr == 0, matrix(0, n), Kr~); }
rowsOf(G, offs, j, W) = { my(o = offs[j], Q = f2annih(W, o[2]), Gj = matrix(o[2], #G, r, c, G[o[1] + r, c])); Q * Gj; }
dimX(G, offs, locs, P) = {
  my(R = matrix(0, #G));
  foreach (P, j, R = matconcat([R; rowsOf(G, offs, j, locs[j])]));
  #G - matrank(Mod(R, 2));
}
{
  for (k = 0, 1,
    my(D = read(Str("selmer_injectivity_places_twist", k, ".bin")), G = D[1], offs = D[2], locs = D[3], np = #offs, good = List());
    printf("---- twist %d: dim X_all = %d\n", k, dimX(G, offs, locs, [1 .. np]));
    forsubset(np, s, my(P = Vec(s)); if (dimX(G, offs, locs, P) == 19,
      my(minimal = 1); foreach (good, g, if (#setminus(Set(g), Set(P)) == 0, minimal = 0)); if (minimal, listput(good, P))));
    foreach (good, g, printf("  minimal with dim 19: %s\n", g));
    for (j = 1, np, printf("  without place %d: dim X = %d\n", j, dimX(G, offs, locs, [i | i <- [1 .. np], i != j]))));
}
quit;
