# Idris2-Ocaml

An OCaml backend for [Idris2](https://github.com/idris-lang/Idris2).

## Requirements

- recent Idris 2 compiler, known to work with 0.2.1-56209de4c
- OCaml, known to work with 4.10.0
- [Zarith](https://github.com/ocaml/Zarith) findable by `ocamlfind` and usable with `ocamlopt` (needs `.cmxa` file, it seems like `*-devel` versions in Linux package managers work fine)
- installed `idris2api` package for the appropriate Idris2 version

## Building

The following command will build the backend and install the support files in the Idris2 "home" directory. Check the [`Makefile`](Makefile) for the location.

(**NOTE**: I am using VScode and the IDE mode process spawned often causes my RAM to fill and use up swap, so the build command kills all open Idris processes before building)

```bash
make IDRIS2_SOURCE_PATH=path/to/idris2/source all
```

The `IDRIS2_SOURCE_PATH` is needed because the runtime C library headers are needed for foreign functions to work.

## Attribution

The files `OcamlRts.ml`, `ocaml_rts.c` are directly taken from the [malfunction backend by ziman and makx](https://github.com/ziman/idris2-mlf).

The Idris module `Ocaml.Modules` uses some adapted code from the same malfunction backend.

## License

Right now this code is licensed under the [Peer Production License](https://wiki.p2pfoundation.net/Peer_Production_License).

Eventually when this code is good enough for inclusion in or endorsement by the Idris2 compiler, the license will change to MIT.
