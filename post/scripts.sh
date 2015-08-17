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
        done <<< "$result" 
    fi
fi

rm result.txt