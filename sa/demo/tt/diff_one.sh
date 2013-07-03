diff tests/$2.out tests/$2.ref  > _XYZ
if [ -s _XYZ ]
then
echo =======
echo " $2  "
echo =======
cat _XYZ
fi