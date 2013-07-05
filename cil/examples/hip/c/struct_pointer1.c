struct item {
  struct item *next;
};

void main()
{
  struct item a;
  return;
}

/*
  Expected output:
  -----
  data item
  {
    item next;
  }

  int main ()
  {
    item a;
    return 1;
  }
*/
