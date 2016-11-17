#!/bin/sh

SEED="HAPPY"

for FMT in sf js sl slk; do
  mkdir -p "benchs/$FMT"
  echo "Creating benchmarks in \"$FMT\" format:"
  echo "  \"spaguetti\" benchmarks..."
  ./spaguetti.pl -s "$SEED" -f "$FMT" -N 1000 -n 10 -lp 0.10 -np 0.20 > "benchs/$FMT/spaguetti-10.$FMT"
  ./spaguetti.pl -s "$SEED" -f "$FMT" -N 1000 -n 11 -lp 0.09 -np 0.15 > "benchs/$FMT/spaguetti-11.$FMT"
  ./spaguetti.pl -s "$SEED" -f "$FMT" -N 1000 -n 12 -lp 0.09 -np 0.11 > "benchs/$FMT/spaguetti-12.$FMT"
  ./spaguetti.pl -s "$SEED" -f "$FMT" -N 1000 -n 13 -lp 0.08 -np 0.11 > "benchs/$FMT/spaguetti-13.$FMT"
  ./spaguetti.pl -s "$SEED" -f "$FMT" -N 1000 -n 14 -lp 0.07 -np 0.11 > "benchs/$FMT/spaguetti-14.$FMT"
  ./spaguetti.pl -s "$SEED" -f "$FMT" -N 1000 -n 15 -lp 0.06 -np 0.12 > "benchs/$FMT/spaguetti-15.$FMT"
  ./spaguetti.pl -s "$SEED" -f "$FMT" -N 1000 -n 16 -lp 0.05 -np 0.17 > "benchs/$FMT/spaguetti-16.$FMT"
  ./spaguetti.pl -s "$SEED" -f "$FMT" -N 1000 -n 17 -lp 0.05 -np 0.13 > "benchs/$FMT/spaguetti-17.$FMT"
  ./spaguetti.pl -s "$SEED" -f "$FMT" -N 1000 -n 18 -lp 0.04 -np 0.20 > "benchs/$FMT/spaguetti-18.$FMT"
  ./spaguetti.pl -s "$SEED" -f "$FMT" -N 1000 -n 19 -lp 0.04 -np 0.15 > "benchs/$FMT/spaguetti-19.$FMT"
  ./spaguetti.pl -s "$SEED" -f "$FMT" -N 1000 -n 20 -lp 0.04 -np 0.11 > "benchs/$FMT/spaguetti-20.$FMT"
  echo "  \"bolognesa\" benchmarks..."
  ./bolognesa.pl -s "$SEED" -f "$FMT" -N 1000 -n 10 -d 10 -p 0.70 > "benchs/$FMT/bolognesa-10.$FMT"
  ./bolognesa.pl -s "$SEED" -f "$FMT" -N 1000 -n 11 -d 11 -p 0.69 > "benchs/$FMT/bolognesa-11.$FMT"
  ./bolognesa.pl -s "$SEED" -f "$FMT" -N 1000 -n 12 -d 12 -p 0.69 > "benchs/$FMT/bolognesa-12.$FMT"
  ./bolognesa.pl -s "$SEED" -f "$FMT" -N 1000 -n 13 -d 13 -p 0.70 > "benchs/$FMT/bolognesa-13.$FMT"
  ./bolognesa.pl -s "$SEED" -f "$FMT" -N 1000 -n 14 -d 14 -p 0.69 > "benchs/$FMT/bolognesa-14.$FMT"
  ./bolognesa.pl -s "$SEED" -f "$FMT" -N 1000 -n 15 -d 15 -p 0.69 > "benchs/$FMT/bolognesa-15.$FMT"
  ./bolognesa.pl -s "$SEED" -f "$FMT" -N 1000 -n 16 -d 16 -p 0.69 > "benchs/$FMT/bolognesa-16.$FMT"
  ./bolognesa.pl -s "$SEED" -f "$FMT" -N 1000 -n 17 -d 17 -p 0.71 > "benchs/$FMT/bolognesa-17.$FMT"
  ./bolognesa.pl -s "$SEED" -f "$FMT" -N 1000 -n 18 -d 18 -p 0.70 > "benchs/$FMT/bolognesa-18.$FMT"
  ./bolognesa.pl -s "$SEED" -f "$FMT" -N 1000 -n 19 -d 19 -p 0.70 > "benchs/$FMT/bolognesa-19.$FMT"
  ./bolognesa.pl -s "$SEED" -f "$FMT" -N 1000 -n 20 -d 20 -p 0.70 > "benchs/$FMT/bolognesa-20.$FMT"
  echo "  \"clone\" benchmarks..."
  ./sl2clone.pl -f "$FMT" -n 01 ./smallfoot-vc/*.sl > "benchs/$FMT/clones-01.$FMT"
  ./sl2clone.pl -f "$FMT" -n 02 ./smallfoot-vc/*.sl > "benchs/$FMT/clones-02.$FMT"
  ./sl2clone.pl -f "$FMT" -n 03 ./smallfoot-vc/*.sl > "benchs/$FMT/clones-03.$FMT"
  ./sl2clone.pl -f "$FMT" -n 04 ./smallfoot-vc/*.sl > "benchs/$FMT/clones-04.$FMT"
  ./sl2clone.pl -f "$FMT" -n 05 ./smallfoot-vc/*.sl > "benchs/$FMT/clones-05.$FMT"
  ./sl2clone.pl -f "$FMT" -n 06 ./smallfoot-vc/*.sl > "benchs/$FMT/clones-06.$FMT"
  ./sl2clone.pl -f "$FMT" -n 07 ./smallfoot-vc/*.sl > "benchs/$FMT/clones-07.$FMT"
  ./sl2clone.pl -f "$FMT" -n 08 ./smallfoot-vc/*.sl > "benchs/$FMT/clones-08.$FMT"
  ./sl2clone.pl -f "$FMT" -n 09 ./smallfoot-vc/*.sl > "benchs/$FMT/clones-09.$FMT"
  ./sl2clone.pl -f "$FMT" -n 10 ./smallfoot-vc/*.sl > "benchs/$FMT/clones-10.$FMT"
done