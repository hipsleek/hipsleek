#!/bin/bash
export LC_ALL=C

SB=./songbird
OPT=""
STAT=""
SUITE=""
LOG=""
PID=$$
LOGDIR="./logs"

# printing function
log_res () {
  printf "$1"
  if [[ ! -z $LOG ]]; then
    printf "$1" >> $LOG
  fi
}

list_descendants ()
{
  local children=$(ps -o pid= --ppid "$1")

  for pid in $children
  do
    list_descendants "$pid"
  done

  echo "$children"
}

print_usage ()
{
  printf "Run test songbird\n\n"
  printf " Usage:\n"
  printf "   run_songbird.sh <options>\n\n"
  printf " Options:\n"
  printf "   -p <prover>        : set prover path\n"
  printf "   -b <benchmark>     : choose benchmark folder\n"
  printf "   -o <options>       : options to be passed to Songbird\n"
  printf "   -l <log>           : output to a log file\n\n"
  printf " Sample commands:\n"
  printf "   nohup ./run_songbird.sh -p ../songbird.byte\
 -b slrd-lm -o \"-lms\" -l \"log-1.log\" &\n"
  exit 0;
}

trap 'echo "";\
      echo Terminating process due to CTRL-C; \
      echo Kill child processes;\
      pkill -TERM -P $PID;\
      exit' INT

if [[ $# = 0 ]]; then
  print_usage
fi

while [[ $# > 0 ]]
do
  key="$1"

  case $key in
    -h|--help)
      print_usage
      ;;
    -p|--prover)
      SB="$2"
      shift # past argument
      ;;
    -b|--bench)
      SUITE="$2"
      shift # past argument
      ;;
    -o|--option)
      OPT=$OPT"$2 "
      shift # past argument
      ;;
    -s|--stat)
      OPT=$OPT"--sb-stats "
      STAT="$1"
      ;;
    -l|--log)
      LOG="$2"
      # shift # past argument
      ;;
    *) # unknown option
      ;;
  esac
  shift # past argument or value
done

echo "My PID is $PID"

if [ ! -d "$SUITE" ]; then
  echo "Error: benchmark '$SUITE' not found!"
  exit 1;
fi

echo "Evaluating the benchmark '$SUITE'"
echo "Running songbird with $OPT" > $LOG

if [[ ! -z $OPT ]]; then
    echo "Running songbird with $OPT"
fi

if [[ ! -z $LOG ]]; then
  echo "Running Songbird..." > $LOG
  echo "   Benchmark: $SUITE" >> $LOG
  echo "   Options: $OPT" >> $LOG
  echo "" >> $LOG
  date >> $LOG
  echo "" >> $LOG
  echo "Output is written to the log file: $LOG"
  echo ""
fi

# TODO: add commit-revision and running date

log_res "Testcase \tResult \tTime\n\n"

mkdir -p $LOGDIR

for fc in $SUITE/*.sb; do
  filename=$(basename "$fc")
  filenamebase="${filename%.*}"

  out="$LOGDIR/$filename.output.log"
  time="$LOGDIR/$filename.time.log"

  log_res "$filenamebase\t"
  timeout 180 /usr/bin/time -f "%e" $SB $fc $OPT 1>$out 2>$time

  if [ "$?" -eq 124 ]; then
    log_res "TIMEOUT"
  else
    if grep -q "Valid" $out; then
      res="Valid"
    elif grep -q "Invalid" $out; then
      res="Invalid"
    elif grep -q "Fail" $out; then
      res="Fail"
    elif grep -q -i -E 'Exception|Error' $out; then
      res="ERR"
    else res="UNK"
    fi
    runtime=`grep -Po '(?<=Time: ).*' $out`   # read time from output
    # printf -v runtime %.2f "$runtime"
    # read runtime < $time   # read time from file
    log_res "$res\t$runtime"
  fi

  if [ ! -z $STAT ]; then
    imply_cnt=$(grep "Number of pure implication" $out | cut -d ":" -f 2)
    cache_hit_cnt=$(grep "Number of cache hit" $out | cut -d ":" -f 2)
    external_prover_cnt=$(grep "Number of external prover call"
                          $out | cut -d ":" -f 2)
    log_res "\t$imply_cnt\t$cache_hit_cnt\t$external_prover_cnt"
  fi

  log_res "\n"

done;
