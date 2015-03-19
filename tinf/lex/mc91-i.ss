int mc91_i (int n)
  infer [@term]
  //infer []
  requires true
  ensures true;
  
  //requires Term
  //ensures true;
  
{
  int c = 1;
  while (c > 0) 
    infer [@term]
    //infer []
    requires true
    ensures true;
    /*
    case {
      c <= 0 -> requires Term ensures true;
      c > 0 -> case {
        n <= 89 -> requires Term[100-n] ensures true;
        90 <= n & n <= 100 -> requires Term[180 + 21*c - 2*n] ensures true;
        n > 100 -> case {
          c = 1 -> requires Term ensures true;
          c != 1 -> case {
            n >= 111 -> requires Term[-42 + 21*c] ensures true;
            n <= 110 -> requires Term[180 + 21*c - 2*n] ensures true;
          }
        }
      }
    }
    */
    /*
    case {
      c <= 0 -> requires Term ensures true;
      c >= 1 -> requires Term[90 + 10*c - n, c] ensures true;
    }
    */
  {
    if (n > 100) {
      n = n - 10;
      c = c - 1;
    } else {
      n = n + 11;
      c = c + 1;
    }
  }
  return n;
}
