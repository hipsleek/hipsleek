function two
{
diff tests/slk/$1.out ref/slk/$1.out -b  > _XYZ
if [ -s _XYZ ]
then
echo =============
echo "tmp_cp $1  "
echo =============
cat _XYZ
fi
}
two lab1.slk --dump-proof
two lab2.slk --dump-proof
two lab3.slk --dump-proof
two lab4.slk --dump-proof


