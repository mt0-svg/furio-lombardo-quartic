\\ selmer_space_export.gp: text export of the global generator matrix G (local square class coordinates of the 82
\\ generators of A(S,2) at all places of S and the real places; /tmp/k21c/sel/gens.bin of prym_two_descent_lib.gp sel_gens,
\\ rows checked in an independent review of the 2-descent) and of the local images locs_j and
\\ layout offs_j of sigma_v_injective.gp (/tmp/k21c/sel/selX_k<k>.bin), for an independent recomputation of the Selmer
\\ space X in Sage (selmer_space_check.sage). Writes selmer_space_generators.txt and selmer_space_local_twist<k>.txt in code/second-implementations/selmer-space.
\\ Run from code/second-implementations/selmer-space: gp -q selmer_space_export.gp
default(parisizemax, 4*10^9); default(nbthreads, 1);
{
  my(G = read("/tmp/k21c/sel/gens.bin")[1], fn = "selmer_space_generators.txt");
  system(Str("rm -f ", fn)); write(fn, "G = ", lift(Mod(G, 2)), ";");
  printf("G: %d x %d\n", #G~, #G);
  for (k = 0, 1, my(S = read(Str("/tmp/k21c/sel/selX_k", k, ".bin")), offs = S[4], locs = S[5], nms = S[7], f = Str("selmer_space_local_twist", k, ".txt"));
    system(Str("rm -f ", f));
    write(f, "nplaces = ", #locs, ";");
    for (j = 1, #locs,
      write(f, "off", j, " = ", offs[j], ";");
      write(f, "name", j, " = \"", if (j <= #nms, nms[j], Str("real ", j - #nms)), "\";");
      write(f, "loc", j, " = ", if (#locs[j] == 0, "[;]", lift(Mod(locs[j], 2))), ";"));
    write(f, "GX = ", lift(Mod(S[1], 2)), ";");
    write(f, "dX = ", S[8], ";");
    printf("k = %d: %d places, dX = %d\n", k, #locs, S[8]));
}
quit;
