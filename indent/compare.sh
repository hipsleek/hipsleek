for entry in `ls *.ml`; do
  echo ${entry}
  ocp-indent ${entry} > indent/${entry}
done
