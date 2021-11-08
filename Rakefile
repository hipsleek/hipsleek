OPAM_PKGS = [
  "extlib",
  "fileutils",
  "batteries",
  "ocamlgraph",
  "camlp4",
  "xml-light"
]

OCAMLFIND_DEPS = [
  "extlib",
  "fileutils",
  "batteries",
  "ocamlgraph",
  "camlp4",
  "camlp4.lib",
  "xml-light"
]

SRC_DIRS = [
  "src",
  "cil"
]

EXECUTABLES = {
  sleek: "sleek.ml",
  hip: "main.ml"
}

OCAMLBUILD_FLAGS = [
  "-use-ocamlfind",
  OPAM_PKGS.include?("menhir") ? " -use-menhir" : "" ,
  SRC_DIRS.map { |dir| "-I #{dir}" }.join(' '),
  "-j 4",
  "-yaccflag -v",
  "-lexflag -q"
]
def ocamlbuild(debug = false)
  "ocamlbuild #{OCAMLBUILD_FLAGS.join ' '} #{debug ? "-tag 'debug'" : ""}"
end

EXTRA_TAGS = {
  "true" =>
    [
      "warn_error(+4+8+9+11+12+25+28)",
      "warn(-26)"
    ],
  "<src/{parser,parse_fix,parse_fixbag,parse_shape,parse_cmd}.ml>" => "pp(camlp4of)",
  "not(<src/{parser,parse_fix,parse_fixbag,parse_shape,parse_cmd}.ml> or <cil/ocamlutil/errormsg.ml>)" => "pp(cppo -I ../ -D TRACE)",
  "\"joust\"" => "include",
  "\"ints\"" => "include",
  "<dependencies/**/*>" => "not_hygienic",
  "<xml/*.*>" => "not_hygienic",
  "<ppx/*.*>" => "not_hygienic",
  "<omega_modified/**/*>" => "not_hygienic",
  "<z3iw/z3/lib/*.*>" => "not_hygienic",
  "<z3/lib/*.*>" => "not_hygienic",
  "<smt2slk_src/*.*>" => "not_hygienic",
  "<mona-1.4/**/*>" => "not_hygienic",
  "<sw/*>" => "not_hygienic",
  "<smt2slk_src/*>" => "not_hygienic",
  "<lp-ex/*>" => "not_hygienic",
  "<cil/obj/x86_LINUX/*.*>" => "not_hygienic",
  "<{3234,benchmark,bin,bugs,_build,core,cparser,demo,docs,errors,examples,exists,field,guard,hoaegs,_hoaegs,hoaegs-new,html_resources,imm,infer,infinity,inline,label,LDK,lemma,list,misc,mlold,mona-1.4,omega_modified,omega_original,printing,problems,sa,sh_solver,slice,term,synlem,term,test,testing,test_proof,test_proof_backup,tests,tp-mona,tp-redlog,validate,vscomp2010,vsttecomp2012,xml,z3}/*.*>" => "-traverse"
}


# Default to compiling all executables in bytecode mode
task default: EXECUTABLES.keys

# Convenience tasks for bytecode compilation of individual executables

EXECUTABLES.each do |exec_name, _|
  desc "Build bytecode version of #{exec_name}"
  task exec_name => "byte:#{exec_name}"
end

# Convenience tasks for bytecode and native executable compilation

desc "Create bytecode versions of all executables"
task :byte do
  Rake.application.in_namespace(:byte) { |ns| ns.tasks.each { |t| t.invoke } }
end

desc "Create native versions of all executables"
task :native do
  Rake.application.in_namespace(:native) { |ns| ns.tasks.each { |t| t.invoke } }
end

# Tasks for compiling bytecode executables

namespace :byte do
  EXECUTABLES.each do |exec_name, entry_pt|
    ocamlbuild_byte_target = entry_pt.ext "byte"

    desc "Build bytecode version of #{exec_name}"
    task exec_name => [".merlin", "_tags"] do
      sh("#{ocamlbuild} #{ocamlbuild_byte_target}")
      sh("mv #{ocamlbuild_byte_target} #{exec_name}")
    end
  end
end

# Tasks for compiling native executables

namespace :native do
  EXECUTABLES.each do |exec_name, entry_pt|
    ocamlbuild_native_target = entry_pt.ext "native"

    desc "Build native version of #{exec_name}"
    task "#{exec_name}" => [".merlin", "_tags"] do
      sh("#{ocamlbuild} #{ocamlbuild_native_target}")
      sh("mv #{ocamlbuild_native_target} #{exec_name}")
    end
  end
end

# Tasks for debug builds

namespace :debug do
  EXECUTABLES.each do |exec_name, entry_pt|
    ocamlbuild_byte_target = entry_pt.ext "byte"

    desc "Build bytecode version of #{exec_name} with debugging symbols"
    task exec_name => [".merlin", "_tags"] do
      sh("#{ocamlbuild true} #{ocamlbuild_byte_target}")
      sh("mv #{ocamlbuild_byte_target} #{exec_name}")
    end
  end
end

desc "Remove build artifacts"
task :clean do
  sh "ocamlbuild -clean"
end

# OPAM dependencies-related tasks

namespace :dependencies do
  desc "Install all OPAM dependencies"
  task :install do
    sh "opam install #{OPAM_PKGS.join ' '}"
  end
end

def test_flow(folder)
  data_regex = "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"

  proc_regex_false_negative = /Procedure [a-zA-Z0-9_]*fail[$][a-zA-Z0-9_]* SUCCESS/
  proc_regex_false_positive = /Procedure [a-zA-Z0-9_]*safe[$][a-zA-Z0-9_]* FAIL/
  lemma_regex_false_negative = /Entailing lemma [a-zA-Z0-9_>-]*fail[:] Valid/
  lemma_regex_false_positive = /Entailing lemma [a-zA-Z0-9_>-]*safe[:] Fail/

  test_folder = "info-test/#{folder}"
  if Dir.exist? test_folder
    puts "Testing #{folder}..."
    Dir.glob("#{test_folder}/*.ss").each do |f|
      puts "- Testing #{f}"
      res = `./hip #{f} | grep "Procedure\\\|Stop\\\|Total verification\\\|Time spent\\\|Z3 Prover\\\|lemma"`

      res.split("\n").map do |line|
        puts "#{line} :: (-)" if line.match(proc_regex_false_negative)
        puts "#{line} :: (+)" if line.match(proc_regex_false_positive)
        puts "#{line} :: (-)" if line.match(lemma_regex_false_negative)
        puts "#{line} :: (+)" if line.match(lemma_regex_false_positive)
      end
    end
  else
    fail IOError, "Folder #{test_folder} does not exist"
  end
end

namespace :test do
  namespace :info_flow do
    task :vmcai do
      test_flow "hip"
    end

    task :eximpf do
      test_flow "eximpf"
    end
  end

  task info_flow: %w[info_flow:vmcai info_flow:eximpf]

  namespace :infer do
    task :shape do
      sh "mkdir res"
      Dir.glob("examples/working/infer/sa/*.c") do |f|
        sh "./hip #{f} &> res/#{File.basename f, '.c'}.res"
      end
    end
  end

  namespace :fast do
    CATEGORIES =
      [
        "hip_tr",
        "hip",
        "imm",
        "imm-filed",
        "sleek",
        "parahip",
        "hip_baga",
        "sleek_threads",
        "hip_threads",
        "hip_vperm",
        "sleek_vperm",
        "sleek_fracperm",
        "sleek_veribsync",
        "hip_veribsync",
        "infinity",
        "mem",
        "coqinf",
        "sleek_infer"
      ]

    CATEGORIES.each do |category|
      desc "Run #{category} tests"
      task category do
        Dir.chdir "examples/working" do
          sh "./run-fast-tests.pl -root ../../ #{category}"
        end
      end
    end
  end
end

# Useful Ocamlbuild rules

rule "inferred.mli" do |task|
  sh "#{ocamlbuild} #{task.name}"
  generated_file = Dir.glob("_build/**/#{task.name}").first

  sh "cp #{generated_file} #{task.name}"
end

rule ".byte" do |task|
  sh "#{ocamlbuild} #{task.name}"
end

rule ".native" do |task|
  sh "#{ocamlbuild} #{task.name}"
end

rule ".depends" do |task|
  sh "#{ocamlbuild} #{task.name}"
end


# Support file generation

desc "Generate merlin file, overwriting any existing merlin configuration"
task ".merlin" do |task|
  merlin_file = task.name

  src_lines_comment = ["# Source directories"]
  src_lines = src_lines_comment + SRC_DIRS.map { |dir| "S #{dir}/" }
  src_lines = src_lines.join("\n") + "\n\n"

  build_line_comment = ["# Build directories"]
  build_line = build_line_comment + ["B _build/**/*"]
  build_line = build_line.join("\n") + "\n\n"

  dep_lines_comment = ["# Dependencies"]
  dep_lines = dep_lines_comment + ["PKG " + OCAMLFIND_DEPS.join(" ")]
  dep_lines = dep_lines.join("\n") + "\n\n"

  flags = [
    "-debug locate,/tmp/merlin-debug"
  ]
  flg_lines_comment = ["# Extra flags"]
  flg_lines = flg_lines_comment + flags.map { |f| "FLG #{f}" }
  flg_lines = flg_lines.join "\n"

  merlin_config = src_lines + build_line + dep_lines + flg_lines

  unless File.exists?(merlin_file) && (File.read(merlin_file) == merlin_config)
    File.write merlin_file, merlin_config + "\n"
  end
end

desc "Generate _tags for ocamlbuild, overwriting any existing _tags file"
task "_tags" do |task|
  tags_file = task.name

  default_tags = [
    "bin_annot",
    *OCAMLFIND_DEPS.map { |dep| "package(#{dep})"}
  ]

  raw_tags = EXTRA_TAGS.clone
  raw_tags['true'] = Array(raw_tags['true']).push *default_tags

  tags = raw_tags.map do |(pred, t)|
    "#{pred}: #{Array(t).join(', ')}"
  end.join "\n"

  unless File.exists?(tags_file) && (File.read(tags_file) == tags)
    File.write tags_file, tags + "\n"
  end
end

namespace :commit do
  task :prep do
    sh "cp -a src/. ./"
  end

  task :end do
    sh "rm *.ml"
    sh "rm *.mll"
    sh "rm *.mly"
  end
end
