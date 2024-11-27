import json, sys, os, shutil

REDLOG_DEPENDENT_PREFIX = "redlog/"

def path_to_sleek_file(proj_root: str, test_group: str, test_name: str):
    prefix = os.path.join(proj_root, "examples", "working")
    if test_group == "sleek":
        prefix = os.path.join(prefix, "sleek")
    elif test_group  == "musterr":
        prefix = os.path.join(prefix, "errors")
    else:
        prefix = os.path.join(prefix, "sleek", test_group)
    return os.path.join(prefix, test_name)

def populate_test_directory(test, proj_root: str, test_group: str, test_directory: str, postprocessor: str):
    source_file = path_to_sleek_file(proj_root, test_group, test["name"])
    shutil.copy(source_file, test_directory)
    shutil.copy(postprocessor, test_directory)

    if REDLOG_DEPENDENT_PREFIX in test_directory:
        sleek_exec = os.path.join("..", "..", "..", proj_root, "sleek.exe")
    else:
        sleek_exec = os.path.join("..", "..", proj_root, "sleek.exe")

    with open(os.path.join(test_directory, "run.t"), "w") as cram_file:
        write_cram_test(cram_file, test, sleek_exec, test_group, postprocessor)

def write_cram_test(test_file, test, sleek_exec, test_group, postprocessor):
    print("This test was automatically generated from the corresponding example in examples/working/.\n", file=test_file)
    copied_name = os.path.basename(test["name"])
    test_flags = test["flags"]
    postprocess_command = f"./{os.path.basename(postprocessor)}"
    print(f"  $ {sleek_exec} {test_flags} {copied_name} | {postprocess_command} ", file=test_file)
    # if test.entailments has a non-empty element:
    if test["entailments"] and test["entailments"][0]:
        for i, result in enumerate(test["entailments"]):
            print(f"  Entail {i+1}: {result}", file=test_file)
    if "lemmas" in test:
        # This does not include the lemma name, which is not filtered out with the preprocessor.
        # Currently, the lemma name has to be semi-manually added in using `dune promote`.
        for i, result in enumerate(test["lemmas"]):
            print(f"  Lemma <{i}>: {result}", file=test_file)

def fixcalc_disable_rules(to_disable: list[str]):
  rules = f"""
(cram
  (applies_to {' '.join(to_disable)})
  (enabled_if %{{bin-available:fixcalc}}))\n"""
  rules += '\n'.join([f"""
(rule
  (alias {test})
  (enabled_if (not %{{bin-available:fixcalc}}))
  (action (echo "\n\nWARNING: fixcalc not found, skipping {test}\n\n"))) """ for test in to_disable])
  return rules




HIP_TEST_DUNE = """
(rule
  (alias runtest)
  (action (echo "\n\nWARNING: redcsl not found, tests for ParaHIP and other related systems will not be run.\n\n"))
  (enabled_if (not %{bin-available:redcsl}))) """\
          + fixcalc_disable_rules(["infer-app-inv", "infer-app-inv2"]) + \
"""(cram
    (deps %{project_root}/sleek.exe)
    (applies_to :whole_subtree))"""

REDLOG_TEST_DUNE = """
(cram
    (enabled_if %{bin-available:redcsl}))"""

def write_dune_files(directory: str):
    # Currently, all configuration is written to the parent directory.
    with open(os.path.join(directory, "dune"), "w") as dune:
        print(HIP_TEST_DUNE, file=dune)

    with open(os.path.join(directory, REDLOG_DEPENDENT_PREFIX, "dune"), "w") as dune:
        print(REDLOG_TEST_DUNE, file=dune)

def main(manifest: str, proj_root: str, directory: str, postprocessor: str):
    redlog_dir = os.path.join(directory, REDLOG_DEPENDENT_PREFIX)
    if os.path.exists(directory):
        shutil.rmtree(directory)

    used_directories = {}
    os.mkdir(directory)
    os.mkdir(redlog_dir)
    write_dune_files(directory)

    with open(manifest, "r") as extracted:
        tests = json.load(extracted)
        for sleek_test in tests["sleek"]:
            test_directory_name = sleek_test["name"].replace(".slk", "").replace("../", "").replace("/", "-")
            if test_directory_name in used_directories:
                used_directories[test_directory_name] += 1
                test_directory_name += f"{used_directories[test_directory_name]}"
            else:
                used_directories[test_directory_name] = 0

            test_directory_name += ".t"
            print(f"Writing directory test {test_directory_name}", file=sys.stderr)
            if "-tp parahip" in sleek_test["flags"] or "-tp redlog" in sleek_test["flags"]:
                test_directory_path = os.path.join(redlog_dir, test_directory_name)
            else:
                test_directory_path = os.path.join(directory, test_directory_name)

            os.mkdir(test_directory_path)
            populate_test_directory(sleek_test, proj_root, "sleek", test_directory_path, postprocessor)


if __name__ == "__main__":
    if len(sys.argv) < 4:
        print(f"usage: {sys.argv[0]} [.json file to parse] [project root] [directory to write tests to] [postprocessor]")
        sys.exit(1)
    manifest, proj_root, directory, postprocessor = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
    main(manifest, proj_root, directory, postprocessor)
