data item {
  inline item next;
}

int main() {
  item ptr;
  return 1;
}

/*

struct {
  struct {
   int p
  } q;
  int v;
} *ptr;

data typ1 {
  int p
}
data typ2 {
  inline typ1 q;
  int v;
}
typ2 ptr;


struct {
  struct {
   int p
  } *q;
  int v;
} *ptr;


data typ1 {
  int p
}
data typ2 {
  typ1 q;
  int v;
}
typ2 ptr;

*/
