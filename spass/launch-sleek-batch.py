import getopt, sys, time, subprocess, os

# command: python launch-sleek-batch "sleek -tp 'prover name'" "<file_contains_list_of_input_file_for_sleek>"
def main():
	try:
		opts, args = getopt.getopt(sys.argv[1:], "", [] )
	except getopt.GetoptError, err:
		# print help information and exit:
		print str(err) # will print something like "option -a not recognized"
		usage()
		sys.exit(2)
	basic_command = args[0]	# "sleek -tp 'prover name'"
	batch_file_name = args[1]		# "<file_contains_list_of_input_file_for_sleek>"
	# get list of input file for sleek
	f = open(batch_file_name, "r");
	input_file_lists = []	
	while 1:
		line = f.readline();
		if not line:
			break
		input_file_lists = input_file_lists + [line.rstrip()]
	# get prover name
	prover_name = "unknown"
	if (basic_command.find("spass") >= 0):
		prover_name = "spass"
	elif (basic_command.find("z3") >= 0):
		prover_name = "z3"
	elif ((basic_command.find("-tp") < 0) or (basic_command.find("oc") >= 0)):
		prover_name = "omega"
	print prover_name		
	# starting to check problems
	summary_file = batch_file_name + ".summary" + "." + prover_name 
	f1 = open(summary_file, "w")
	f1.write("Problem name, Running time\n")
	f1.write("\n")
	f1.close()
	for input_file in input_file_lists:
		output_file = input_file + ".out." + prover_name 
		command = basic_command + " " + input_file + " > " + output_file
		print ""
		print ("Start running command: " + str(command))
		sys.stdout.flush()
		start_time = time.time ()
		os.system(command)
		stop_time = time.time ()
		print "----------------------------------------------------"
		duration = stop_time - start_time
		print ("Running time: " + str(duration) + " seconds.")
		# write to log file
		f = open(output_file, "a")
		f.write("\n----------------\n")
		f.write("Running time:" + str(duration) + " seconds.")
		f.close()
		# write to summary file
		f1 = open(summary_file, "a")
		f1.write(input_file + ", " + str(duration) + "\n")
		f1.close()

if __name__ == "__main__":
    main()

