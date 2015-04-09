for entry in `ls *.ml`; do
  case "$entry" in
      (*"parse"*) echo "excluding : parse matched $entry";;
      (*)         echo "$entry"; ocp-indent -i ${entry} ;
  esac
done
