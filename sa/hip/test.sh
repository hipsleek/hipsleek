DIR=../../

for FILE in `find . -name 'll-append*.ss'`; do 
	FNAME=$(basename "$FILE")
	FNAME=${FNAME%.*}
	echo $FNAME
	SFILE=$FNAME".ss"
	CPFILE=$FNAME".cp"
	CMD="../../hip $SFILE -cp-constrs $CPFILE"
	RES="$($CMD)"
	if [[ $RES == *INVALID* ]]
	then
	    echo "### invalid"
	else
	    	if [[ $RES == *VALID* ]]
		then	
			echo "### valid"
		else
			echo "### not found"
		fi	
	fi
done
