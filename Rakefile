OPAM_PKGS = [
  "extlib",
  "batteries",
  "ocamlgraph.1.8.5",
  "camlp4",
  "xml-light"
]

OCAMLFIND_DEPS = [
  "extlib",
  "batteries",
  "ocamlgraph",
  "camlp4",
  "camlp4.lib",
  "xml-light"
]

SRC_DIRS = [
]

EXECUTABLES = {
}

OCAMLBUILD_FLAGS = [
  "-use-ocamlfind",
  OPAM_PKGS.include?("menhir") ? " -use-menhir" : "" ,
  SRC_DIRS.map { |dir| "-I #{dir}" }.join(' '),
  "-j 4",
  "-yaccflag -v",
  "-lexflag -q"
]

EXTRA_TAGS = {
  "true" => ["warn_error(+4+8+9+11+12+25+28)", "warn(-26)"],
  "<{parser,parse_fix,parse_fixbag,parse_shape,parse_cmd}.ml>" => "pp(camlp4of)",
  "not(<{parser,parse_fix,parse_fixbag,parse_shape,parse_cmd}.ml> or <cil/ocamlutil/errormsg.ml>)" => "pp(cppo -I ../ -D TRACE)"
}



task default: [:sleek, :hip]

task :hip do
  sh "ocamlbuild -use-ocamlfind main.byte"
  sh "cp main.byte hip"
end

task :sleek do
  sh "ocamlbuild -use-ocamlfind sleek.byte"
  sh "cp sleek.byte sleek"
end

task :clean do
  sh "ocamlbuild -clean"
end

eximpf_test_files =
  [
    "info-test/eximpf/double_if.ss",
    "info-test/eximpf/double_if_precise.ss",
    "info-test/eximpf/lemma.ss",
    "info-test/eximpf/ll_length.ss",
    "info-test/eximpf/ll_concat.ss",
    "info-test/eximpf/ll_sum.ss",
    "info-test/eximpf/pred_id.ss",
    "info-test/eximpf/pred_cast.ss",
    "info-test/eximpf/pred_unfold.ss",
    "info-test/eximpf/mutual_exclusive.ss",
    "info-test/eximpf/equal_branches.ss"
  ]
hip_test_files =
  [
    "info-test/hip/double_if_precise.ss",
    "info-test/hip/double_if.ss",
    "info-test/hip/lemma.ss",
    "info-test/hip/ll_length.ss",
    "info-test/hip/ll_concat.ss",
    "info-test/hip/ll_sum.ss",
    "info-test/hip/pred_id.ss",
    "info-test/hip/pred_cast.ss",
    "info-test/hip/pred_unfold.ss",
    "info-test/hip/mutual_exclusive.ss",
    "info-test/hip/equal_branches.ss"
  ]

task :test_info_flow do
  data_regex = "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"

  proc_regex_false_negative = /Procedure [a-zA-Z0-9_]*fail[$][a-zA-Z0-9_]* SUCCESS/
  proc_regex_false_positive = /Procedure [a-zA-Z0-9_]*safe[$][a-zA-Z0-9_]* FAIL/
  lemma_regex_false_negative = /Entailing lemma [a-zA-Z0-9_>-]*fail[:] Valid/
  lemma_regex_false_positive = /Entailing lemma [a-zA-Z0-9_>-]*safe[:] Fail/

  puts "Testing eximpf..."
  Dir.glob("info-test/eximpf/*.ss").each do |f|
    puts "- Testing #{f}"
    res = `./hip #{f} | grep "Procedure\\\|Stop\\\|Total verification\\\|Time spent\\\|Z3 Prover\\\|lemma"`

    res.split("\n").map do |line|
      puts "#{line} :: (-)" if line.match(proc_regex_false_negative)
      puts "#{line} :: (+)" if line.match(proc_regex_false_positive)
      puts "#{line} :: (-)" if line.match(lemma_regex_false_negative)
      puts "#{line} :: (+)" if line.match(lemma_regex_false_positive)
    end
  end

  puts "Testing hip..."
  Dir.glob("info-test/hip/*.ss").each do |f|
    puts "- Testing #{f}"
    res = `./hip #{f} | grep "Procedure\\\|Stop\\\|Total verification\\\|Time spent\\\|Z3 Prover\\\|lemma"`

    res.split("\n").map do |line|
      puts "#{line} :: (-)" if line.match(proc_regex_false_negative)
      puts "#{line} :: (+)" if line.match(proc_regex_false_positive)
      puts "#{line} :: (-)" if line.match(lemma_regex_false_negative)
      puts "#{line} :: (+)" if line.match(lemma_regex_false_positive)
    end
  end
end

rule ".mli" do |task|
  sh "ocamlbuild -use-ocamlfind #{task.name.ext "inferred.mli"}"
end
