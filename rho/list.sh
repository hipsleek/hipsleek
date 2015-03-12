for entry in `ls -d1 */ | egrep -v "logs|ref|result"`; do
  echo mkdir -p ref/${entry}
  echo mkdir -p result/${entry}
done
for entry in `ls */*.ss`; do
  echo \$EX ${entry}
done
