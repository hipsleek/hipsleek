sed -E 's/Entailing lemma/Lemma/g' \
  | grep -E '^(Entail|Lemma)' \
  | sed -E 's/\..*$//g' \
  | sed -E 's/^(Entail|Lemma) \(([0-9]+)\)/\1 \2/g' \
  | sed -E 's/^(Entail|Lemma) ([0-9]+) /\1 \2/g' \
  | sort -s -k1,1
