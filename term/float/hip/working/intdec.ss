/* decrease examples */
/*
// hip
void foo(int x)
    case
    {
      x <= 1 -> requires Term ensures true;
      x > 1  -> requires Term[x] ensures true;
    }
{
  if (x > 1)
  {
    foo(x-1);
  }
}
*/

/* sleek */

// 1
checkentail (x <= 1) & Term & (x > 1) & (x1 = x-1) & (x1 <= 1) 
                      |- Term.

// 2 - why Term |- Term[x1] valid?
checkentail (x <= 1) & Term & (x > 1) & (x1 = x-1) & (x1 > 1)
                      |- Term[x1].

checkentail (x <= 1) & (x > 1) & (x1 = x-1) & (x1 > 1)
                      |- false.
                      
// 3 - fail
checkentail (x > 1) & Term[x] & (x > 1) & (x1 = x-1)  & (x1 <= 1)
                      |- Term.


// 4 - fail
checkentail (x > 1) & Term[x] & (x > 1) & (x1 = x-1) & (x1 > 1)
                      |- Term[x1].

