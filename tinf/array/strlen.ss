
int randInt() 
  requires true
  ensures true;

int[] alloc(int ind)
 requires ind>0
  ensures true;


int str_len(int[] p,int i)
 requires true
  ensures true;
{
  if (p[i]==0) return 0;
  else return 1 + str_len(p,i+1);
}

int main() 
  requires true
  ensures true;

{
  int length1 = randInt();
     if (length1 < 1) {
         length1 = 1;
     }
     int[] nondetString1 = alloc(length1);
     nondetString1[length1-1] = 0;
     int i=0;
     str_len(nondetString1,i);
}

/*
# strlen.ss

why is there a hd exception/

Checking procedure main$... 
Procedure main$ FAIL.(2)

Exception Failure("hd") Occurred!
(Program not linked with -g, cannot print stack backtrace)

*/
