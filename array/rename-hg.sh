
for entry in `ls */*/*.ref2`; do
 echo hg rename ${entry} $(echo ${entry} | sed 's/ref2$/ref/g')
 #`hg rename ${entry} $(echo ${entry} | sed 's/ref2$/ref/g')`
done
