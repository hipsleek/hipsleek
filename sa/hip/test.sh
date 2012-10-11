DIR=/home/phuong/Workspace/sa/sleekex/
TDIR=/home/phuong/Workspace/sa/sleekex/sa/hip/


for FILE in `find $TDIR -name 'll-append*.ss'`; do 
	FNAME=$(basename "$FILE")
	FNAME=${FNAME%.*}
	echo $FNAME
	echo "================="
	SFILE=$TDIR$FNAME".ss"
	CPFILE=$TDIR$FNAME".cp"
	CMD=$DIR"hip $SFILE -cp-constrs $CPFILE"
	RES="$($CMD)"
	if [[ $RES == *BEGIN-CMP* ]]
	then
	  	TMP="${RES#*BEGIN-CMP}"
		NRES="${TMP%END-CMP*}"
		echo "$NRES"
	else    	
		echo "### not found"
	fi
done
