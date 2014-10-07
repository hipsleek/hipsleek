struct item
{
  struct item **next; // TODO: how to convert?
};

int main()
{
  struct item a;
  return 1;
}

/*
  Expected output:
  -----
  data item
  {
    ????????    // TODO: how to convert?
  }

  int main ()
  {
    item a;
    return 1;
  }
*/
