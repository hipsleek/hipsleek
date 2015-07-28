# When called with "-dre analyse_param",
# hip will include trace like:
#   (==...==)
#   analyse_param@1
#   analyse_param inp1 : INPUT1
#   analyse_param inp2 : INPUT2
#   analyse_param EXIT: OUTPUT
# This awk script filters out the other lines,
# and prints the above like:
#   Analyse Param:
#   inp1 : INPUT1
#   inp2 : INPUT2
#   EXIT: OUTPUT

/^analyse_param/ {
    $1="";
    # sub(FS,""); # Get rid of first space (i.e. field separator)
    if ($0)
        print;
    else
        print "Analyse Param:";
}
