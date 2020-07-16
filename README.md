# Installation Guide for hip/sleek

## Normal Installation
1. Compile Omega modified as follows:
   ```
   cd omega_modified
   make oc
   ```
   The omega executable is now in `omega_calc/obj/oc`.
   Please move it to some default location,
   such as `/usr/local/bin`.

2. Compile Mona as follows:
   ```
   tar -xvf mona-1.4-modif.tar.gz
   cd mona-1.4
   ./install.sh
   ```
   The mona executable is now placed in
   `/usr/local/bin`.

3. Please install latest Ocaml compiler in your directory.
   Please also install Coq prover.

4. You are now ready to install hip/sleek, as follows:
   ```
   cd ..
   make

   The executables `hip` and `sleek` can now be used (or moved
   to `/usr/local/bin`)

5. Sleek examples can be found in `examples/working/sleek`
   subdirectory. You can test it as follows:

   1. Entailment using default Omega
      ```
      ./sleek examples/working/sleek/sleek2.slk
      ```

   2. Entailment using Mona
      ```
      ./sleek -tp mona examples/working/sleek/sleek2.slk
      ```

   3. Verification using default Omega
      ```
      ./hip examples/working/hip/ll.ss
      ```

   4. Verification using Mona
      ```
      ./hip -tp mona examples/working/hip/ll.ss
      ```

## Installation with [hipsleek/dependencies]
This process should work on an Ubuntu-like system.
1. Clone this repository with `git clone --recursive https://github.com/hipsleek/dependencies`.
1. Install [hipsleek/dependencies].
1. Install [hipsleek/hipsleek].

## Omega for MAC:
(by Yahui Song, 25th May 2020, e0210374@u.nus.edu,
email me if you have difficulties compiling on mac)

1. uncompress this `omega_modified_for_mac.zip` folder and use it to replace your `omega_modified` folder under `sleekex/`
2. run
   ```
   cd omega_modified
     make depend
   cd omega_calc/obj
   make
   sudo cp oc /usr/local/bin/
   ```
3. and then you go back and make the sleekex again.

[hipsleek/dependencies]: https://github.com/hipsleek/dependencies
[hipsleek/hipsleek]: https://github.com/hipsleek/hipsleek
