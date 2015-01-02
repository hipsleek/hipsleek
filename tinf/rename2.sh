
for entry in `ls */*/*.out2`; do
 `mv ${entry} $(echo ${entry} | sed 's/out2$/out/g')`
 #echo mv ${entry} $(echo ${entry} | sed 's/out$/ss.out/g')
 #`hg rename ${entry} $(echo ${entry} | sed 's/ref2$/ref/g')`
done
