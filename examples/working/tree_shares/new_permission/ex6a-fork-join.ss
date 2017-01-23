data cell {int val;}

               macro L == (#,)
               macro R == (,#)
               macro LL == ((#,),)
               macro LR == ((,#),)
               macro RL == (,(#,))
               macro RR == (,(,#))

               /*
               void destroyCell(ref cell ce)
               requires ce::cell(c,t,a)<_> & c=t+a
               ensures ce'=null;//'

               // WRAPPER FUNCTION
               cell newCell(int bound,int value)
               requires bound>0
               ensures res::cell(bound,bound,0)<value>;
               */

               void thread1(cell x, ref int y)
               requires x::cell(@@L)<n>
               ensures x::cell(@@L)<n> & y'= n+1;//'
               {
                y=x.val+1;
                }

               /*
               void thread2(cell x, ref int z)
               requires x::cell<5>
               ensures x::cell<5> & z'=4;//'
               {
                z=x.val-1;
                }

               void thread3(cell x, ref int t)
               requires true
               ensures t'=10;//'
               {
                t=10;
                }
               */

               void main(cell x)
               requires x::cell<n>
               ensures x::cell<n>;
               {
                //  int y,z,t;
                    int y;
                    //  x.val = 5;
                    int id1 = fork(thread1,x,y);
                    // int id2 = fork(thread2,x,z);
                    //  int id3 = fork(thread3,x,t);
                    join(id1);
                    //  join(id2);
                    //  join(id3);
                    //  int tmp = x.val;
                    // assert(tmp'=5);
                    // destroyCell(x);
                    //  assert(y'=6 & z'=4 & t'=10);
                    }
