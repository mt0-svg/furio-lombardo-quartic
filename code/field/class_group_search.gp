\\ class_group_search.gp: class group data of K21 used to search the certificates (writes field_bnf.bin, not tracked:
\\ 900 KB). The certificates are checked in Lean, so the GRH-conditional bnf needs no certification.
default(parisizemax, 4*10^9); default(nbthreads, 1);
f = x^21 - 7*x^20 + 14*x^19 - 84*x^16 + 98*x^15 + 2*x^14 + 175*x^13 - 609*x^12 + 980*x^11 - 770*x^10 - 280*x^9 + 1008*x^8 - 1072*x^7 + 560*x^6 + 28*x^5 - 336*x^4 + 252*x^3 - 112*x^2 + 28*x - 4;
out = if (#getenv("BNFOUT"), getenv("BNFOUT"), "field_bnf.bin");
bnf = bnfinit(f, 1);
print("h = ", bnf.no, "  cyc = ", bnf.cyc);
writebin(out, bnf);
quit
