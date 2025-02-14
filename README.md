# Mechanized Uniform Interpolation in Intuitionistic and Modal Logics

This project formalizes the construction of uniform interpolants for basic
modal logic K, Gödel-Löb provability logic GL, and intuitionistic strong Löb
logic iSL. The latter includes the calculation of uniform interpolants for
intuitionistic logic IL.

## Online calculator

A uniform interpolant calculator is available here:

[https://hferee.github.io/UIML/demo.html](https://hferee.github.io/UIML/demo.html)

The calculator parses an input formula and computes the uniform interpolants for the
various logics listed above.

This calculator was built by extracting the relevant Coq functions to OCaml code, which is then
further compiled to Javascript.

## Building

Compiling the project requires Coq version 8.19.2 and may not compile on other versions. One may enforce this locally by running
`opam pin coq 8.19.2` in the project folder.

There is a rudimentary install script `install.sh` in this folder.

### Dependencies

The proof library depends on `coq` and `coq-stdpp`.

Building the demo further requires `js_of_ocaml` and `angstrom`.

All of the above are available on `opam`.

### Instruction

The proof library compiles with `make`.
The documentation builds with `make doc`.

## Command Line Tools

Aside from the online demo, we provide a set of command line tools. Running them with no arguments will print a description.

- `uiml_cmdline s n` : Computes the uniform interpolants of `n` formulas chosen from an enumeration, with `s` being the start index of that enumeration.
- `isl_simp f` : Simplifies the formula `f` in iSL.
- `isl_dec f` : Decides the provability of the modal formula `f` in iSL.
- `benchmark` : Runs a set of benchmarks.

## Documentation

The documentation generated by `coqdoc` is available here:
[https://hferee.github.io/UIML/toc.html](https://hferee.github.io/UIML/toc.html)
