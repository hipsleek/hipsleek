struct value {
  int x;
  int y;
};
  

struct item {
  struct item *next;
  struct value *v;
};

void main()
{
  struct item a;
  return;
}

/*
  Expected output:
  -----
  data value {
    int x;
    int y;
  }
  
  data item {
    item next;
    value v;
  }

  int main ()
  {
    item a;
    return 1;
  }
*/
