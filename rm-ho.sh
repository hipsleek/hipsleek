sed -f rm-ho.sed $1 > $1-new
sed -n -f rm-ho2.sed $1 > $1-diff
