\\ selmer_injectivity_places.gp: which local conditions of the 2-Selmer computation (prym_two_descent.gp) are needed for the
\\ injectivity of Sel^2 -> H(f_v) at the place v above 2 with e = 3?
\\ Input: the caches of p21_29 / p21_31 (/tmp/k21c/sel/gens.bin: G, the 164 x 82 local coordinate matrix of the
\\ generators of A(S,2) = L(S,2) x N(S,2); selX_k<k>.bin: offsets, local images and K_w^x images per place).
\\ Exports G and the per place data to selmer_injectivity_places_twist<k>.bin in this directory (small, for reproducibility).
\\ For every subset P of the places other than v, X_P = {x in A(S,2) : res_w(x) in W_w for w in P}; the kernel of
\\ res_v on X_P modulo the image of K(S,2) is trivial iff dim {x in X_P : res_v(x) in KM_v} = 15.
\\ Run: gp -q selmer_injectivity_places.gp
default(parisizemax, 3*10^9); default(nbthreads, 1);
SEL = "/tmp/k21c/sel/";
f2annih(W, n) = { if (#W == 0, return(matid(n))); my(Kr = lift(matker(Mod(W~, 2)))); if (#Kr == 0, matrix(0, n), Kr~); }
rowsOf(G, offs, j, W) = { my(o = offs[j], Q = f2annih(W, o[2]), Gj = matrix(o[2], #G, r, c, G[o[1] + r, c])); Q * Gj; }
dimK(G, offs, locs, KMs, iv, P) = {
  my(R = rowsOf(G, offs, iv, KMs[iv]));
  foreach (P, j, R = matconcat([R; rowsOf(G, offs, j, locs[j])]));
  #G - matrank(Mod(R, 2));
}
{
  my(GG = read(Str(SEL, "gens.bin")), G = GG[1]);
  printf("G: %d x %d, rank %d\n", #G~, #G, matrank(Mod(G, 2)));
  for (k = 0, 1,
    my(S = read(Str(SEL, "selX_k", k, ".bin")), offs = S[4], locs = S[5], KMs = S[6], nms = S[7], np = #offs, iv, others);
    writebin(Str("selmer_injectivity_places_twist", k, ".bin"), [G, offs, locs, KMs, nms]);
    printf("---- twist %d: %d places\n", k, np);
    for (j = 1, np, printf("  place %d: %s, offset %s, dim W = %d, dim KM = %d\n", j, if (j <= #nms, nms[j], "real"), offs[j], #locs[j], #KMs[j]));
    iv = [j | j <- [1 .. np], offs[j][2] == 22]; if (#iv != 1, error("v not unique")); iv = iv[1];
    others = [j | j <- [1 .. np], j != iv];
    printf("  all places: dim {x in X : res_v x in KM_v} = %d (15 means injective)\n", dimK(G, offs, locs, KMs, iv, others));
    forsubset(#others, s, my(P = vector(#s, i, others[s[i]]), d = dimK(G, offs, locs, KMs, iv, P));
      if (d == 15, printf("  sufficient: %s -> %d\n", P, d)));
    foreach (others, j, my(P = [i | i <- others, i != j]); printf("  drop place %d: %d\n", j, dimK(G, offs, locs, KMs, iv, P))));
}
quit;
