
for entry in `ls */*/*.slk.out`; do
  echo ${entry}
  echo $(echo ${entry} | sed 's/slk.out$/slk.out2/g')
done
