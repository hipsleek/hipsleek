SLEEK_TIMEOUT=2.0

echo "**********************" >> timeout.out
date >> timeout.out
echo "**********************" >> timeout.out

kill_proc () {
	killall -v oc
	killall -v reduce
	killall -v SPASS-MOD
	killall -v sleek
}

for (( i = 10; i <= 20; i++ ))
do
	# Omega
	# echo "[oc][.nslc] spaguetti-$i"
	# echo "[oc][.nslc] spaguetti-$i" >> timeout.out
	# kill_proc
	# time (../../../../sleek --ufdp spaguetti-$i.slk --eps --dis-slicing --dis-imm --dis-provers-timeout --sleek-timeout $SLEEK_TIMEOUT) 1> spaguetti-$i.oc.nslc.to 2>> timeout.out

	# echo "[oc][.slc] spaguetti-$i"
	# echo "[oc][.slc] spaguetti-$i" >> timeout.out
	# kill_proc
	# time (../../../../sleek --ufdp spaguetti-$i.slk --eps --dis-imm --dis-provers-timeout --sleek-timeout $SLEEK_TIMEOUT) 1> spaguetti-$i.oc.slc.to 2>> timeout.out
	# # time (../../../../sleek --ufdp spaguetti-20-551-1000.slk --eps --dis-imm --dis-provers-timeout --sleek-timeout $SLEEK_TIMEOUT) 1> spaguetti-$i.oc.slc.to 2>> timeout.out
	
	# echo "[oc][.ineq] spaguetti-$i"
	# echo "[oc][.ineq] spaguetti-$i" >> timeout.out
	# kill_proc
	# time (../../../../sleek --ufdp spaguetti-$i.slk --eps --enable-slicing --slc-opt-ineq --dis-imm --dis-provers-timeout --sleek-timeout $SLEEK_TIMEOUT) 1> spaguetti-$i.oc.ineq.to 2>> timeout.out

	echo "[oc][.ineq.1] spaguetti-$i"
	echo "[oc][.ineq.1] spaguetti-$i" >> timeout.out
	kill_proc
	time (../../../../sleek --ufdp spaguetti-$i.slk --eps --enable-slicing --getctr-n 1 --slc-opt-ineq --dis-imm --dis-provers-timeout --sleek-timeout $SLEEK_TIMEOUT) 1> spaguetti-$i.oc.ineq.1.to 2>> timeout.out
	
	echo "[oc][.ineq.2] spaguetti-$i"
	echo "[oc][.ineq.2] spaguetti-$i" >> timeout.out
	kill_proc
	time (../../../../sleek --ufdp spaguetti-$i.slk --eps --enable-slicing --getctr-n 2 --slc-opt-ineq --dis-imm --dis-provers-timeout --sleek-timeout $SLEEK_TIMEOUT) 1> spaguetti-$i.oc.ineq.2.to 2>> timeout.out

	echo "[oc][.ineq.3] spaguetti-$i"
	echo "[oc][.ineq.3] spaguetti-$i" >> timeout.out
	kill_proc
	time (../../../../sleek --ufdp spaguetti-$i.slk --eps --enable-slicing --getctr-n 3 --slc-opt-ineq --dis-imm --dis-provers-timeout --sleek-timeout $SLEEK_TIMEOUT) 1> spaguetti-$i.oc.ineq.3.to 2>> timeout.out

	# Redlog
	# echo "[rl][.nslc] spaguetti-$i"
	# echo "[rl][.nslc] spaguetti-$i" >> timeout.out
	# kill_proc
	# time (../../../../sleek --ufdp -tp redlog --dis-oc spaguetti-$i.slk --eps --dis-slicing --dis-imm --dis-provers-timeout --sleek-timeout $SLEEK_TIMEOUT) 1> spaguetti-$i.rl.nslc.to 2>> timeout.out

	# echo "[rl][.slc] spaguetti-$i"
	# echo "[rl][.slc] spaguetti-$i" >> timeout.out
	# kill_proc
	# time (../../../../sleek --ufdp -tp redlog --dis-oc spaguetti-$i.slk --eps --dis-imm --dis-provers-timeout --sleek-timeout $SLEEK_TIMEOUT) 1> spaguetti-$i.rl.slc.to 2>> timeout.out

	# echo "[rl][.ineq] spaguetti-$i"
	# echo "[rl][.ineq] spaguetti-$i" >> timeout.out
	# kill_proc
	# time (../../../../sleek --ufdp -tp redlog --dis-oc spaguetti-$i.slk --eps --enable-slicing --slc-opt-ineq --dis-imm --dis-provers-timeout --sleek-timeout $SLEEK_TIMEOUT) 1> spaguetti-$i.rl.ineq.to 2>> timeout.out

	# SPASS
	# echo "[spass][.nslc] spaguetti-$i"
	# echo "[spass][.nslc] spaguetti-$i" >> timeout.out
	# kill_proc
	# time (../../../../sleek --ufdp -tp spass spaguetti-$i.slk --eps --dis-slicing --dis-imm --dis-provers-timeout --sleek-timeout $SLEEK_TIMEOUT) 1> spaguetti-$i.spass.nslc.to 2>> timeout.out

	# echo "[spass][.slc] spaguetti-$i"
	# echo "[spass][.slc] spaguetti-$i" >> timeout.out
	# kill_proc
	# time (../../../../sleek --ufdp -tp spass spaguetti-$i.slk --eps --dis-imm --dis-provers-timeout --sleek-timeout $SLEEK_TIMEOUT) 1> spaguetti-$i.spass.slc.to 2>> timeout.out

	# echo "[spass][.ineq] spaguetti-$i"
	# echo "[spass][.ineq] spaguetti-$i" >> timeout.out
	# kill_proc
	# time (../../../../sleek --ufdp -tp spass spaguetti-$i.slk --eps --enable-slicing --slc-opt-ineq --dis-imm --dis-provers-timeout --sleek-timeout $SLEEK_TIMEOUT) 1> spaguetti-$i.spass.ineq.to 2>> timeout.out
	
	# echo "[spass][.nslc] spaguetti-$i"
	# echo "[spass][.nslc] spaguetti-$i" >> timeout.out
	# kill_proc
	# time (../../../../sleek --ufdp -tp spass spaguetti-$i.slk --eps --dis-slicing --dis-provers-timeout --sleek-timeout $SLEEK_TIMEOUT) 1> spaguetti-$i.spass.imm.nslc.to 2>> timeout.out

	# echo "[spass][.slc] spaguetti-$i"
	# echo "[spass][.slc] spaguetti-$i" >> timeout.out
	# kill_proc
	# time (../../../../sleek --ufdp -tp spass spaguetti-$i.slk --eps --dis-imm --dis-provers-timeout --sleek-timeout $SLEEK_TIMEOUT) 1> spaguetti-$i.spass.imm.slc.to 2>> timeout.out

	# echo "[spass][.ineq] spaguetti-$i"
	# echo "[spass][.ineq] spaguetti-$i" >> timeout.out
	# kill_proc
	# time (../../../../sleek --ufdp -tp spass spaguetti-$i.slk --eps --enable-slicing --slc-opt-ineq --dis-imm --dis-provers-timeout --sleek-timeout $SLEEK_TIMEOUT) 1> spaguetti-$i.spass.imm.ineq.to 2>> timeout.out

done

kill_proc
