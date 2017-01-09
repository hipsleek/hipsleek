
            int foo(int x)
            infer [@post_n]
            requires true
            ensures true;
            {
            if (x>2222)
              return x;
             else if (x>0)
             return foo(x-1);
            else
            return x;
            }
