/*
The motivating example in Fig.1
*/

//memory cell
data cell{ int val;}

               //deallocate a cell
               void destroyCell(cell a)
               requires a::cell<_>
               ensures true;

               void thread1(cell x, cell y)
               requires x::cell<0> * y::cell<0>
               ensures x::cell<1> * y::cell<2>;
               {
                x.val = x.val + 1;
                      y.val = y.val + 2;
                      }

               void thread2(cell x, cell y)
               requires x::cell<1> * y::cell<2>
               ensures x::cell<2> * y::cell<4>;
               {
                x.val = x.val + 1;
                      y.val = y.val + 2;
                      }

               void main()
               requires true ensures true;
               {

                cell x = new cell(0);
                     cell y = new cell(0);
                     int t1, t2;

                     t1 = fork(thread1,x,y);
                     t2 = fork(thread2,x,y);

                     join(t1);
                     // x.val = x.val + 1;

                     join(t2);

                     //  assert x'::cell<2> * y'::cell<4>;

                     destroyCell(x);
                     destroyCell(y);
                     }
