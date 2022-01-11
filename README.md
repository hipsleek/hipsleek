
# Installation Guide for HIP/SLEEK

You will need opam and a recent OCaml compiler (tested on 4.12.1).

```sh
# Install opam dependencies
OPAMYES=true rake dependencies:install

# Build everything
rake

# Build only some targets
rake hip
rake sleek

# To use ocamldebug
rake debug:hip debug:sleek
```

Try verifying some small programs.
You will need [Z3](https://github.com/Z3Prover/z3/wiki#platforms) and [Omega](#omega) on the PATH.

```sh
./hip examples/working/hip/ll.ss
./sleek examples/working/sleek/sleek2.slk
```

To run tests,

```sh
# Tested on Perl 5.34
cpanm File::NCopy Spreadsheet::WriteExcel Spreadsheet::ParseExcel

cd examples/working
./run-fast-tests.pl sleek # around 4 mins
./run-fast-tests.pl hip # around 40 mins
```

# External Provers

Executables for custom provers will be installed in their respective directories and should be made available on the PATH, either by appending those directories or moving them some global location like `/usr/local/bin`.

## Omega

```sh
cd omega_modified
make oc
```

The omega executable is now at `omega_calc/obj/oc`.

## Mona

```sh
tar -xvf mona-1.4-modif.tar.gz
cd mona-1.4
./configure --prefix=$(pwd)
make install
cp mona_predicates.mona ..
```

The mona executable is now in `bin`.

Try some tests:

```sh
./hip -tp mona examples/working/hip/ll.ss
./sleek -tp mona examples/working/sleek/sleek2.slk
```

# Installation with [hipsleek/dependencies](https://github.com/hipsleek/dependencies)

This process should work on an Ubuntu-like system.

1. Clone this repository with `git clone --recursive https://github.com/hipsleek/hipsleek`
1. Follow the instructions in the `dependencies` directory
1. Follow the compilation instructions above
