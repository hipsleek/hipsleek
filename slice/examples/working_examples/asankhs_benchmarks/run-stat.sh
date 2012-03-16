TIMEOUT=600

echo "**********************" >> time.stat
date >> time.stat
echo "**********************" >> time.stat

kill_proc () {
	killall -v oc
	killall -v z3
	killall -v reduce
	killall -v SPASS-MOD
	killall -v sleek
}

for (( i = 10; i <= 20; i++ ))
do
	# echo "[z3][.imm.eps] spaguetti-$i"
	# time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --eps > spaguetti-$i.z3.imm.eps
	# echo "[z3][.imm.ineq.eps] spaguetti-$i"
	# time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --eps --enable-slicing --slc-opt-ineq > spaguetti-$i.z3.imm.ineq.eps
	# echo "[z3][.imm.slc.eps] spaguetti-$i"
	# time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --eps --enable-slicing > spaguetti-$i.z3.imm.slc.eps

	# Z3
	echo "[z3][.nslc] spaguetti-$i"
	echo "[z3][.nslc] spaguetti-$i" >> time.stat
	kill_proc
	(time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --eps --dis-slicing --dis-imm --ep-stat) 1> spaguetti-$i.z3.nslc.stat 2>> time.stat

	echo "[z3][.slc] spaguetti-$i"
	echo "[z3][.slc] spaguetti-$i" >> time.stat
	kill_proc
	(time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --eps --enable-slicing --dis-imm --ep-stat) 1> spaguetti-$i.z3.slc.stat 2>> time.stat

	echo "[z3][.ineq] spaguetti-$i"
	echo "[z3][.ineq] spaguetti-$i" >> time.stat
	kill_proc
	(time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --eps --enable-slicing --slc-opt-ineq --dis-imm --ep-stat) 1> spaguetti-$i.z3.ineq.stat 2>> time.stat

	# Omega
	# echo "[oc][.eps] spaguetti-$i"
	# echo "[oc][.eps] spaguetti-$i" >> time.stat
	# killall -v oc
	# time (./timeout -TERM $TIMEOUT ../../../../sleek --ufdp spaguetti-$i.slk --eps --dis-slicing --dis-imm) 1> spaguetti-$i.oc.eps 2>> time.stat

	# echo "[oc][.slc.eps] spaguetti-$i"
	# echo "[oc][.slc.eps] spaguetti-$i" >> time.stat
	# killall -v oc
	# time (./timeout -TERM $TIMEOUT ../../../../sleek --ufdp spaguetti-$i.slk --eps --enable-slicing --dis-imm) 1> spaguetti-$i.oc.slc.eps 2>> time.stat

	# echo "[oc][.ineq.eps] spaguetti-$i"
	# echo "[oc][.ineq.eps] spaguetti-$i" >> time.stat
	# killall -v oc
	# (time ../../../../sleek --ufdp spaguetti-$i.slk --eps --enable-slicing --slc-opt-ineq --dis-imm) 1> spaguetti-$i.oc.ineq.eps 2>> time.stat

	# echo "[z3][] spaguetti-$i"
	# time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --dis-imm > spaguetti-$i.z3
	# echo "[z3][.ineq] spaguetti-$i"
	# time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --enable-slicing --slc-opt-ineq --dis-imm > spaguetti-$i.z3.ineq
	# echo "[z3][.slc] spaguetti-$i"
	# time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --enable-slicing --dis-imm > spaguetti-$i.z3.slc

	# Redlog
	# echo "[rl][.eps] spaguetti-$i"
	# echo "[rl][.eps] spaguetti-$i" >> time.stat
	# killall -v reduce
	# killall -v oc
	# time (./timeout -TERM $TIMEOUT ../../../../sleek --ufdp -tp redlog --dis-oc spaguetti-$i.slk --eps --dis-slicing --dis-imm) 1> spaguetti-$i.rl.eps 2>> time.stat

	# echo "[rl][.slc.eps] spaguetti-$i"
	# echo "[rl][.slc.eps] spaguetti-$i" >> time.stat
	# killall -v reduce
	# killall -v oc
	# time (./timeout -TERM $TIMEOUT ../../../../sleek --ufdp -tp redlog --dis-oc spaguetti-$i.slk --eps --enable-slicing --dis-imm) 1> spaguetti-$i.rl.slc.eps 2>> time.stat

	# echo "[rl][.ineq.eps] spaguetti-$i"
	# echo "[rl][.ineq.eps] spaguetti-$i" >> time.stat
	# killall -v reduce
	# killall -v oc
	# (time ../../../../sleek --ufdp -tp redlog --dis-oc spaguetti-$i.slk --eps --enable-slicing --slc-opt-ineq --dis-imm) 1> spaguetti-$i.rl.ineq.eps 2>> time.stat

done

kill_proc
