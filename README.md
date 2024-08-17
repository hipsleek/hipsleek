
# HIP/SLEEK

## Build

You will need opam and a recent OCaml compiler (tested on 4.14.1).

```sh
opam install . --deps-only
dune build ./hip.exe ./sleek.exe

# To use ocamldebug
rake debug:hip debug:sleek
```

Try verifying some small programs.
You will need Z3 (from opam, pip, or a system package manager) and Omega ([below](#omega)) on the PATH.

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

Other external provers HIP/SLEEK uses can be built from source.
They will be installed in their respective directories and should be made available on the PATH.

Here is an example .envrc file which makes all the provers available, after following the steps below to build each one:

```envrc
eval "$(opam env --switch=4.14.1 --set-switch)"
PATH_add omega_modified/omega_calc/obj
PATH_add mona-1.4/bin
PATH_add fixcalc_src
```

## Omega

```sh
(cd omega_modified; make oc)
```

## Mona

```sh
tar -xvf mona-1.4-modif.tar.gz
cd mona-1.4
./configure --prefix=$(pwd)
make install
cp mona_predicates.mona ..
cd -
```

Try some tests:

```sh
./hip -tp mona examples/working/hip/ll.ss
./sleek -tp mona examples/working/sleek/sleek2.slk
```

## Fixcalc

You will need GHC 9.4.8.

```sh
cabal install --lib regex-compat old-time
cabal install happy
```

Build [Omega](#omega) first. Then, in the hipsleek project directory,

```sh
git clone https://github.com/hipsleek/omega_stub.git
(cd omega_stub; make)

git clone https://github.com/hipsleek/fixcalc.git fixcalc_src
(cd fixcalc_src; make fixcalc)
```
