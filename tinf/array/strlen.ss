
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

void main() 
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

sa_logging branch may have solved this already..

let rec get_failure_list_failesc_context (ls:list_failesc_context): (string* failure_kind)=
    (*may use rand to combine the list first*)
    let los, fks= List.split (List.map get_failure_failesc_context [(List.hd ls)]) in

make gbyte

Exception Failure("hd") Occurred!
Raised at file "pervasives.ml", line 20, characters 22-33
Called from file "cformula.ml", line 10027, characters 68-80
Called from file "typechecker.ml", line 2237, characters 34-73
Called from file "gen.ml", line 1219, characters 14-19
Re-raised at file "gen.ml", line 1225, characters 16-19
Called from file "gen.ml", line 1634, characters 14-17
Re-raised at file "gen.ml", line 1636, characters 34-36
Called from file "typechecker.ml", line 2465, characters 5-27
Called from file "typechecker.ml", line 1256, characters 18-52
Re-raised at file "typechecker.ml", line 1258, characters 61-63
Called from file "gen.ml", line 1219, characters 14-19
Re-raised at file "gen.ml", line 1225, characters 16-19
Called from file "typechecker.ml", line 2310, characters 15-59
Called from file "gen.ml", line 1219, characters 14-19
Re-raised at file "gen.ml", line 1225, characters 16-19
Called from file "gen.ml", line 1634, characters 14-17
Re-raised at file "gen.ml", line 1636, characters 34-36
Called from file "typechecker.ml", line 2465, characters 5-27
Called from file "typechecker.ml", line 1256, characters 18-52
Re-raised at file "typechecker.ml", line 1258, characters 61-63
Called from file "gen.ml", line 1219, characters 14-19
Re-raised at file "gen.ml", line 1225, characters 16-19
Called from file "typechecker.ml", line 1763, characters 16-58
Re-raised at file "typechecker.ml", line 1775, characters 73-75
Called from file "gen.ml", line 1219, characters 14-19
Re-raised at file "gen.ml", line 1225, characters 16-19
Called from file "gen.ml", line 1634, characters 14-17
Re-raised at file "gen.ml", line 1636, characters 34-36
Called from file "typechecker.ml", line 2465, characters 5-27
Called from file "typechecker.ml", line 1256, characters 18-52
Re-raised at file "typechecker.ml", line 1258, characters 61-63
Called from file "gen.ml", line 1219, characters 14-19
Re-raised at file "gen.ml", line 1225, characters 16-19
Called from file "gen.ml", line 1219, characters 14-19
Re-raised at file "gen.ml", line 1225, characters 16-19
Called from file "typechecker.ml", line 1400, characters 31-48
Called from file "others.ml", line 114, characters 16-34
Re-raised at file "others.ml", line 122, characters 16-17
Called from file "typechecker.ml", line 1455, characters 17-62
Called from file "gen.ml", line 1219, characters 14-19
Re-raised at file "gen.ml", line 1225, characters 16-19
Called from file "gen.ml", line 1634, characters 14-17
Re-raised at file "gen.ml", line 1636, characters 34-36
Called from file "typechecker.ml", line 2465, characters 5-27
Called from file "typechecker.ml", line 1256, characters 18-52
Re-raised at file "typechecker.ml", line 1258, characters 61-63
Called from file "gen.ml", line 1219, characters 14-19
Re-raised at file "gen.ml", line 1225, characters 16-19
Called from file "typechecker.ml", line 2310, characters 15-59
Called from file "gen.ml", line 1219, characters 14-19
Re-raised at file "gen.ml", line 1225, characters 16-19
Called from file "gen.ml", line 1634, characters 14-17
Re-raised at file "gen.ml", line 1636, characters 34-36
Called from file "typechecker.ml", line 2465, characters 5-27
Called from file "typechecker.ml", line 1256, characters 18-52
Re-raised at file "typechecker.ml", line 1258, characters 61-63
Called from file "gen.ml", line 1219, characters 14-19
Re-raised at file "gen.ml", line 1225, characters 16-19
Called from file "typechecker.ml", line 2308, characters 16-59
Called from file "gen.ml", line 1219, characters 14-19
Re-raised at file "gen.ml", line 1225, characters 16-19
Called from file "gen.ml", line 1634, characters 14-17
Re-raised at file "gen.ml", line 1636, characters 34-36
Called from file "typechecker.ml", line 2465, characters 5-27
Called from file "typechecker.ml", line 1256, characters 18-52
Re-raised at file "typechecker.ml", line 1258, characters 61-63
Called from file "gen.ml", line 1219, characters 14-19
Re-raised at file "gen.ml", line 1225, characters 16-19
Called from file "typechecker.ml", line 2308, characters 16-59
Called from file "gen.ml", line 1219, characters 14-19
Re-raised at file "gen.ml", line 1225, characters 16-19
Called from file "gen.ml", line 1634, characters 14-17
Re-raised at file "gen.ml", line 1636, characters 34-36
Called from file "typechecker.ml", line 2465, characters 5-27
Called from file "typechecker.ml", line 1256, characters 18-52
Re-raised at file "typechecker.ml", line 1258, characters 61-63
Called from file "gen.ml", line 1219, characters 14-19
Re-raised at file "gen.ml", line 1225, characters 16-19
Called from file "typechecker.ml", line 1763, characters 16-58
Re-raised at file "typechecker.ml", line 1775, characters 73-75
Called from file "gen.ml", line 1219, characters 14-19
Re-raised at file "gen.ml", line 1225, characters 16-19
Called from file "gen.ml", line 1634, characters 14-17
Re-raised at file "gen.ml", line 1636, characters 34-36
Called from file "typechecker.ml", line 2465, characters 5-27
Called from file "typechecker.ml", line 1256, characters 18-52
Re-raised at file "typechecker.ml", line 1258, characters 61-63
Called from file "gen.ml", line 1219, characters 14-19
Re-raised at file "gen.ml", line 1225, characters 16-19
Called from file "typechecker.ml", line 703, characters 34-71
Re-raised at file "typechecker.ml", line 915, characters 83-84
Called from file "typechecker.ml", line 438, characters 198-211
Called from file "typechecker.ml", line 438, characters 198-211
Called from file "others.ml", line 114, characters 16-34
Re-raised at file "others.ml", line 122, characters 16-17
Called from file "typechecker.ml", line 2964, characters 99-150
Re-raised at file "typechecker.ml", line 3286, characters 45-46
Called from file "gen.ml", line 1219, characters 14-19
Re-raised at file "gen.ml", line 1225, characters 16-19
Called from file "typechecker.ml", line 3410, characters 14-63


*/
