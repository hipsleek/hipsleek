#directory="/home/thanhtoantnt/hg/sleekex/examples/"

while getopts ":d:s:p:" o; do
    case "${o}" in
        d)
            d=${OPTARG};;
        s)
            s=${OPTARG} ;;
        p)
            p=${OPTARG} ;;
    esac
done

shift $((OPTIND-1))

if [ $s = "hip" ]; then
    result=$(find $d -type f -name "*.ss");
    if [ $p = "assert-unsound-false" ]; then
        while IFS= read -r line
        do
            ../hip $line --assert-unsound-false > result.txt;
            grep_result=$(grep -n "Unsound false in SLEEK?" result.txt);
            if [ $? -eq 0 ]; then
                echo $line
            fi
            rm result.txt
        done <<< "$result" 
    fi
fi



if [ $s = "sleek" ]; then
    result=$(find $d -type f -name "*.slk");
    if [ $p = "assert-unsound-false" ]; then
        while IFS= read -r line
        do
            ../sleek $line --assert-unsound-false > result.txt;
            grep_result=$(grep -n "Unsound false in SLEEK?" result.txt);
            if [ $? -eq 0 ]; then
                echo $line
            fi
            rm result.txt
        done <<< "$result" 
    fi
fi

if [ $s = "hip" ]; then
    result=$(find $d -type f -name "*.ss");
    if [ $p = "new-estate" ]; then
        while IFS= read -r line
        do
            ../hip $line > result.txt;
            grep_result=$(grep -n "To add this to new_estate.es_infer_rel\|if important : need to add to estate.es_infer_rel" result.txt);
            if [ $? -eq 0 ]; then
                echo $line
            fi
            rm result.txt
        done <<< "$result" 
    fi
fi



if [ $s = "sleek" ]; then
    result=$(find $d -type f -name "*.slk");
    if [ $p = "new-estate" ]; then
        while IFS= read -r line
        do
            ../sleek $line > result.txt;
            grep_result=$(grep -n "To add this to new_estate.es_infer_rel\|if important : need to add to estate.es_infer_rel" result.txt);
            if [ $? -eq 0 ]; then
                echo $line
            fi
            rm result.txt
        done <<< "$result" 
    fi
fi

if [ $s = "hip" ]; then
    result=$(find $d -type f -name "*.ss");
    if [ $p = "false-counting" ]; then
        while IFS= read -r line
        do
            ../hip $line --eps --old-collect-false > result1.txt;
            ../hip $line --eps > result2.txt
            result1=$(grep -F "false context" result1.txt)
            result2=$(grep -F "false context" result2.txt)
            if [ $? -eq 0 ]; then
                initial1=$(echo $result1 | head -c 1);
                initial2=$(echo $result2 | head -c 1);
                if [ "$initial2" -gt "$initial1" ]; then
                    echo $line
                fi
            fi
            rm result1.txt
            rm result2.txt
        done <<< "$result" 
    fi
fi

if [ $s = "sleek" ]; then
    result=$(find $d -type f -name "*.slk");
    if [ $p = "false-counting" ]; then
        while IFS= read -r line
        do
            ../sleek $line --old-collect-false > result1.txt;
            ../sleek $line  > result2.txt
            result1=$(grep -F "false context" result1.txt)
            result2=$(grep -F "false context" result2.txt)
            if [ $? -eq 0 ]; then
                initial1=$(echo $result1 | head -c 1);
                initial2=$(echo $result2 | head -c 1);
                if [ "$initial2" -gt "$initial1" ]; then
                    echo $line
                fi
            fi
            rm result1.txt
            rm result2.txt
        done <<< "$result" 
    fi
fi
