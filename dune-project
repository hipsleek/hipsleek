(lang dune 3.11)

(using dune_site 0.1)

(name hipsleek)
(generate_opam_files true)

(source
 (github hipsleek/hipsleek))

(authors "HIP/SLEEK contributors")

(maintainers "hip.sleek@gmail.com")
(license MIT)


(package
 (name hipsleek)
 (synopsis "Separation logic verifier")
 (description "The HIP/SLEEK separation logic verifier")
 (sites (lib api_prelude))
 (depends
  (dune-site (>= 3.16.0))
  (fileutils (>= 0.6.4))
  (batteries (>= 3.8.0))
  (ocamlgraph (>= 2.1.0))
  (camlp4 (>= 4.14+1))
  (xml-light (>= 2.5))
  (ppx_expect (>= v0.15.1))
))

