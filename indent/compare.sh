for entry in `ls *.ml`; do
  echo ${entry}
  #ocp-indent ${entry} > indent/${entry}
  diff -u ${entry} ../${entry}
done
