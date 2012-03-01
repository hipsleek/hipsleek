import getopt, sys, time, subprocess


def main():
	try:
		opts, args = getopt.getopt(sys.argv[1:], "", [] )
	except getopt.GetoptError, err:
		# print help information and exit:
		print str(err) # will print something like "option -a not recognized"
		usage()
		sys.exit(2)
	command = args[0].split(" ")
	print (" Start running command: " + str(command))
	print "----------------------------------------------------"
	start_time = time.time ()
	subprocess.call(command)
	stop_time = time.time ()
	print "----------------------------------------------------"
	duration = stop_time - start_time
	print " Total time: " + str(duration) + " seconds."

if __name__ == "__main__":
    main()

