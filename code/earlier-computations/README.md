# The data pipeline

The exact data that the programs writing the Lean data start from, and the PARI/GP scripts of this repository that wrote them (`code/README.md` lists the files whose writer is not shipped). `data/` holds the lattice data, the centres, the Selmer images at v and the box lists of the recorded runs, and `export/` the PARI/GP values at the centres. Every script is run from this directory with `gp -q <script> < /dev/null`, as its header says.

## The cache directory

The scripts of the pipeline below keep their intermediate results under `/tmp/k21c/`:

- `nr/`: the field N of degree 84, its factorisations and its S-units;
- `sel/`: the 2-Selmer computation over K and the lattice at v;
- `sat/`: the square roots found by the saturation, so that a rerun of `sunits_n84_saturate.gp` resumes;
- `m9e/`: the box lists.

`sunits_n84_saturate.gp`, `prym_two_descent.gp`, `sigma_v_injective.gp` and `boxes.gp` create the directories they write; run `mkdir -p /tmp/k21c/nr` before the first step. Several scripts read a cache file instead of recomputing it when it is present (`sunits_n84.gp`, `sunits_n84_saturate.gp`, the functions of `prym_two_descent_lib.gp`); remove `/tmp/k21c` to run everything from the start.

## Run order

| Step | Script                                                                 | Reads                                                                                                                        | Writes                                                                                                 |
| ---- | ---------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------ |
| 1    | `bruin_form_reduce.gp`                                                 | `bruin_form_orbit21.gp`, `prym_lib.gp`                                                                                       | `bruin_form.gp` (output `bruin_form_reduce.out`)                                                       |
| 2    | `field_n84_galois.gp`                                                  | `field_kprime_data.gp`, `field_l42_polynomial.gp`, `field_n84_polynomial.gp`                                                 | `nr/nfN.bin`, `nr/faL_N.bin`, `nr/fa13_N.bin`, `nr/bnf13.bin`, `nr/P13.gp` (no recorded output)        |
| 3    | `sunits_n84.gp`                                                        | `field_l42_polynomial.gp`, `field_n84_polynomial.gp`, `field_k13_polynomial.gp`, `norm_relation_lib.gp`, the files of step 2 | `nr/nsunits.bin` (output `sunits_n84.out`)                                                             |
| 4    | `sunits_n84_saturate.gp`                                               | `nr/nsunits.bin`, `nr/nfN.bin`, `field_n84_polynomial.gp`, `norm_relation_lib.gp`                                            | `nr/nsat.bin`, `sat/` (output `sunits_n84_saturate.out`)                                               |
| 5    | `prym_two_descent.gp`, with the functions of `prym_two_descent_lib.gp` | the files of steps 2 to 4, `local_images_twist*_e*.bin`                                                                      | `sel/fields.bin`, `sel/places.bin`, `sel/gens.bin`, `sel/loccache.bin` (output `prym_two_descent.out`) |
| 6    | `sigma_v_injective.gp`                                                 | the caches of step 5, `local_images_twist*_e*.bin`                                                                           | `sel/selX_k<k>.bin` (output `sigma_v_injective.out`)                                                   |
| 7    | `selmer_image_v.gp`                                                    | `sel/selX_k<k>.bin`, `local_images_twist<k>_e3.bin`                                                                          | `sel/rho_k<k>.bin`, recorded as `data/selmer_image_v_twist<k>.bin` (output `selmer_image_v.out`)       |
| 8    | `chabauty_lattice.gp`                                                  | `sel/rho_k<k>.bin`, `local_images_twist<k>_e3.bin`, `genus2_log_kv.gp`, `phi_known_lifts.gp`, `pullback_known_lifts.gp`      | `sel/lattice_k<k>.bin` (output `chabauty_lattice.out`)                                                 |
| 9    | `boxes.gp`, with `leading_class_explore.gp`                            | `sel/lattice_k<k>.bin`                                                                                                       | `m9e/boxes_k<k>.txt`, recorded as `data/boxes_twist<k>.txt` (output `boxes.out`)                       |

`sunits_n84.gp` ends with a failed check: its S-units reach character rank 46, and the check asks for 53. It writes `nr/nsunits.bin` before that check, and `sunits_n84_saturate.gp` completes the basis to rank 53 and ends with RESULT PASS.

## Other files

- `lattice_cert.gp` reads `local_images_twist*_e3.bin` and `data/selmer_image_v_twist*.bin` and writes `data/lattice_twist*.bin`; `centres_cert.gp` reads them, `data/boxes_twist*.txt` and `export/centres_pari_twist*.txt`, and writes `data/centres_twist*.txt`.
- `discs_q2.gp` writes the discs of C(Q_2) in `discs_q2.txt`.
- `completion_kv.gp` (the field K_v), `abel_prym_lib.gp`, `genus2_log_kv.gp`, `norm_relation_lib.gp` and `prym_lib.gp` are libraries.
- `class_group_l42_two.gp` and `class_group_n84_two.gp` are cited by `FurioLombardo/M3b/Hypotheses.lean`.
