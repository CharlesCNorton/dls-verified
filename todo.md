# todo

- Re-base the computational core on binary N arithmetic with transport lemmas from the nat layer, so the Extract Constant maps and their unproven semantic claims retire.
- Compile the calculator through a machine-checked pipeline, whether MetaCoq verified extraction to OCaml or CertiCoq to CompCert C, and gate the cutover on a bit-identical oracle corpus against the classical extraction.
