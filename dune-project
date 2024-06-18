(lang dune 3.11)

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
 (depends
  (extlib (>= 1.7.9))
  (fileutils (>= 0.6.4))
  (batteries (>= 3.8.0))
  (ocamlgraph (>= 2.1.0))
  (camlp4 (>= 4.14+1))
  (xml-light (>= 2.5))))
