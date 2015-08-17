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
            grepresult=$(grep -n "Unsound false in SLEEK?" result.txt);
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
            grepresult=$(grep -n "Unsound false in SLEEK?" result.txt);
            if [ $? -eq 0 ]; then
                echo $line
            fi
        done <<< "$result" 
    fi
fi