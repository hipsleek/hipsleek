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

task :vmcai_benchmark do
  data_regex = "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"

  proc_regex_false_negative = /Procedure [a-zA-Z0-9_]*fail[$][a-zA-Z0-9_]* SUCCESS/
  proc_regex_false_positive = /Procedure [a-zA-Z0-9_]*safe[$][a-zA-Z0-9_]* FAIL/
  lemma_regex_false_negative = /Entailing lemma [a-zA-Z0-9_>-]*fail[:] Valid/
  lemma_regex_false_positive = /Entailing lemma [a-zA-Z0-9_>-]*safe[:] Fail/
  z3_regex_time = /Stop z3... (\d*) invocations/
  omega_regex_time = /Stop Omega... (\d*) invocations/
  total_regex_time = /Total verification time: (\d+)\.(\d+)/

  puts "VMCAI Benchmark..."
  puts "Test Names \t False Positive \t False Negative \t Total \t Z3 \t Omega \t Time (Seconds)"
  Dir.glob("info-test/hip/*.ss").each do |f|
    res = `./hip #{f} | grep "Procedure\\\|Stop\\\|Total verification\\\|lemma"`
    fp  = 0
    fn  = 0
    tot = 0
    z3  = 0
    omg = 0
    time1 = 0
    time2 = 0

    res.split("\n").map do |line|
      if line.match(proc_regex_false_negative)
        fn = fn + 1
      end
      if line.match(lemma_regex_false_negative)
        fn = fn + 1
      end
      if line.match(proc_regex_false_positive)
        fp = fp + 1
      end
      if line.match(lemma_regex_false_positive)
        fp = fp + 1
      end
      if line.match(z3_regex_time)
        z3 = line.match(z3_regex_time)[1]
      else
        if line.match(omega_regex_time)
          omg = line.match(omega_regex_time)[1]
        else
          if line.match(total_regex_time)
            time1 = line.match(total_regex_time)[1]
            time2 = line.match(total_regex_time)[2]
          else
            tot = tot + 1
          end
        end
      end
    end
    puts "#{f} \t #{fp} \t #{fn} \t #{tot} \t #{z3} \t #{omg} \t #{time1}.#{time2}"
  end
end

task :eximpf_single_benchmark do
  data_regex = "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"

  proc_regex_false_negative = /Procedure [a-zA-Z0-9_]*fail[$][a-zA-Z0-9_]* SUCCESS/
  proc_regex_false_positive = /Procedure [a-zA-Z0-9_]*safe[$][a-zA-Z0-9_]* FAIL/
  lemma_regex_false_negative = /Entailing lemma [a-zA-Z0-9_>-]*fail[:] Valid/
  lemma_regex_false_positive = /Entailing lemma [a-zA-Z0-9_>-]*safe[:] Fail/
  z3_regex_time = /Stop z3... (\d*) invocations/
  omega_regex_time = /Stop Omega... (\d*) invocations/
  total_regex_time = /Total verification time: (\d+)\.(\d+)/

  puts "EXIMPF Benchmark..."
  puts "Test Names \t False Positive \t False Negative \t Total \t Z3 \t Omega \t Time (Seconds)"
  Dir.glob("info-test/eximpf/if_rewrite.ss").each do |f|
    fp  = 0
    fn  = 0
    tot = 0
    z3_tmp = 0
    z3  = 0
    omg_tmp = 0
    omg = 0
    time1 = 0
    time2 = 0
    time1_tmp = 0;
    time2_tmp = 0;
    time_total = 0;
    loop = 0
    max_loop = 10;

    while loop < max_loop do
      res = `./hip #{f} | grep "Procedure\\\|Stop\\\|Total verification\\\|lemma"`
      res.split("\n").map do |line|
        if line.match(proc_regex_false_negative)
          fn = fn + 1
        end
        if line.match(lemma_regex_false_negative)
          fn = fn + 1
        end
        if line.match(proc_regex_false_positive)
          fp = fp + 1
        end
        if line.match(lemma_regex_false_positive)
          fp = fp + 1
        end
        if line.match(z3_regex_time)
          z3_tmp = line.match(z3_regex_time)[1]
          z3_tmp = z3_tmp.to_i
          z3 = z3 + z3_tmp
        else
          if line.match(omega_regex_time)
            omg_tmp = line.match(omega_regex_time)[1]
            omg_tmp = omg_tmp.to_i
            omg = omg + omg_tmp
          else
            if line.match(total_regex_time)
              time1_tmp = line.match(total_regex_time)[1].to_i
              time2_tmp = line.match(total_regex_time)[2].to_i
              time1 = ((time1_tmp*100)+time2_tmp+0.0)/100
              puts "#{time1} #{time2}"
              time2 = time2 + time1
            else
              tot = tot + 1
            end
          end
        end
      end
      loop = loop + 1
    end
    fp = fp/max_loop
    fn = fn/max_loop
    z3 = z3/max_loop
    omg = omg/max_loop
    time2 = time2/max_loop
    tot = tot/max_loop
    puts "#{f} \t #{fp} \t #{fn} \t #{tot} \t #{z3} \t #{omg} \t #{time2}"
  end
end

task :eximpf_benchmark do
  data_regex = "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"

  proc_regex_false_negative = /Procedure [a-zA-Z0-9_]*fail[$][a-zA-Z0-9_]* SUCCESS/
  proc_regex_false_positive = /Procedure [a-zA-Z0-9_]*safe[$][a-zA-Z0-9_]* FAIL/
  lemma_regex_false_negative = /Entailing lemma [a-zA-Z0-9_>-]*fail[:] Valid/
  lemma_regex_false_positive = /Entailing lemma [a-zA-Z0-9_>-]*safe[:] Fail/
  z3_regex_time = /Stop z3... (\d*) invocations/
  omega_regex_time = /Stop Omega... (\d*) invocations/
  total_regex_time = /Total verification time: (\d+)\.(\d+)/

  puts "EXIMPF Benchmark..."
  puts "Test Names \t False Positive \t False Negative \t Total \t Z3 \t Omega \t Time (Seconds)"
  Dir.glob("info-test/eximpf/*.ss").each do |f|
    res = `./hip #{f} | grep "Procedure\\\|Stop\\\|Total verification\\\|lemma"`
    fp  = 0
    fn  = 0
    tot = 0
    z3  = 0
    omg = 0
    time1 = 0
    time2 = 0

    res.split("\n").map do |line|
      if line.match(proc_regex_false_negative)
        fn = fn + 1
      end
      if line.match(lemma_regex_false_negative)
        fn = fn + 1
      end
      if line.match(proc_regex_false_positive)
        fp = fp + 1
      end
      if line.match(lemma_regex_false_positive)
        fp = fp + 1
      end
      if line.match(z3_regex_time)
        z3 = line.match(z3_regex_time)[1]
      else
        if line.match(omega_regex_time)
          omg = line.match(omega_regex_time)[1]
        else
          if line.match(total_regex_time)
            time1 = line.match(total_regex_time)[1]
            time2 = line.match(total_regex_time)[2]
          else
            tot = tot + 1
          end
        end
      end
    end
    puts "#{f} \t #{fp} \t #{fn} \t #{tot} \t #{z3} \t #{omg} \t #{time1}.#{time2}"
  end
end

task :all_benchmark do
  data_regex = "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"

  proc_regex_false_negative = /Procedure [a-zA-Z0-9_]*fail[$][a-zA-Z0-9_]* SUCCESS/
  proc_regex_false_positive = /Procedure [a-zA-Z0-9_]*safe[$][a-zA-Z0-9_]* FAIL/
  lemma_regex_false_negative = /Entailing lemma [a-zA-Z0-9_>-]*fail[:] Valid/
  lemma_regex_false_positive = /Entailing lemma [a-zA-Z0-9_>-]*safe[:] Fail/
  z3_regex_time = /Stop z3... (\d*) invocations/
  omega_regex_time = /Stop Omega... (\d*) invocations/
  total_regex_time = /Total verification time: (\d+)\.(\d+)/
  max_loop = 25;

  puts "EXIMPF Benchmark..."
  puts "Test Names \t False Positive \t False Negative \t Total \t Z3 \t Omega \t Time (Seconds)"
  Dir.glob("info-test/eximpf/*.ss").each do |f|
    fp  = 0
    fn  = 0
    tot = 0
    z3_tmp = 0
    z3  = 0
    omg_tmp = 0
    omg = 0
    time1 = 0
    time2 = 0
    time1_tmp = 0;
    time2_tmp = 0;
    time_total = 0;
    loop = 0

    while loop < max_loop do
      res = `./hip #{f} | grep "Procedure\\\|Stop\\\|Total verification\\\|lemma"`
      res.split("\n").map do |line|
        if line.match(proc_regex_false_negative)
          fn = fn + 1
        end
        if line.match(lemma_regex_false_negative)
          fn = fn + 1
        end
        if line.match(proc_regex_false_positive)
          fp = fp + 1
        end
        if line.match(lemma_regex_false_positive)
          fp = fp + 1
        end
        if line.match(z3_regex_time)
          z3_tmp = line.match(z3_regex_time)[1]
          z3_tmp = z3_tmp.to_i
          z3 = z3 + z3_tmp
        else
          if line.match(omega_regex_time)
            omg_tmp = line.match(omega_regex_time)[1]
            omg_tmp = omg_tmp.to_i
            omg = omg + omg_tmp
          else
            if line.match(total_regex_time)
              time1_tmp = line.match(total_regex_time)[1].to_i
              time2_tmp = line.match(total_regex_time)[2].to_i
              time1 = ((time1_tmp*100)+time2_tmp+0.0)/100
              time2 = time2 + time1
            else
              tot = tot + 1
            end
          end
        end
      end
      loop = loop + 1
    end
    fp = fp/max_loop
    fn = fn/max_loop
    z3 = z3/max_loop
    omg = omg/max_loop
    time2 = time2/max_loop
    tot = tot/max_loop
    puts "#{f} \t #{fp} \t #{fn} \t #{tot} \t #{z3} \t #{omg} \t #{time2}"
  end

  puts "VMCAI Benchmark..."
  puts "Test Names \t False Positive \t False Negative \t Total \t Z3 \t Omega \t Time (Seconds)"
  Dir.glob("info-test/hip/*.ss").each do |f|
    fp  = 0
    fn  = 0
    tot = 0
    z3_tmp = 0
    z3  = 0
    omg_tmp = 0
    omg = 0
    time1 = 0
    time2 = 0
    time1_tmp = 0;
    time2_tmp = 0;
    time_total = 0;
    loop = 0

    while loop < max_loop do
      res = `./hip #{f} | grep "Procedure\\\|Stop\\\|Total verification\\\|lemma"`
      res.split("\n").map do |line|
        if line.match(proc_regex_false_negative)
          fn = fn + 1
        end
        if line.match(lemma_regex_false_negative)
          fn = fn + 1
        end
        if line.match(proc_regex_false_positive)
          fp = fp + 1
        end
        if line.match(lemma_regex_false_positive)
          fp = fp + 1
        end
        if line.match(z3_regex_time)
          z3_tmp = line.match(z3_regex_time)[1]
          z3_tmp = z3_tmp.to_i
          z3 = z3 + z3_tmp
        else
          if line.match(omega_regex_time)
            omg_tmp = line.match(omega_regex_time)[1]
            omg_tmp = omg_tmp.to_i
            omg = omg + omg_tmp
          else
            if line.match(total_regex_time)
              time1_tmp = line.match(total_regex_time)[1].to_i
              time2_tmp = line.match(total_regex_time)[2].to_i
              time1 = ((time1_tmp*100)+time2_tmp+0.0)/100
              time2 = time2 + time1
            else
              tot = tot + 1
            end
          end
        end
      end
      loop = loop + 1
    end
    fp = fp/max_loop
    fn = fn/max_loop
    z3 = z3/max_loop
    omg = omg/max_loop
    time2 = time2/max_loop
    tot = tot/max_loop
    puts "#{f} \t #{fp} \t #{fn} \t #{tot} \t #{z3} \t #{omg} \t #{time2}"
  end
end

rule ".mli" do |task|
  sh "ocamlbuild -use-ocamlfind #{task.name.ext "inferred.mli"}"
end
