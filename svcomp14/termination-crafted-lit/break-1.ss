
int nondet_int()
  requires true
  ensures true;

int main() {
    int x = nondet_int();
    while (x > 0 && x < 100) {
        int old_x = x;
        x = nondet_int();
        if (x < 2*old_x + 10) {
            break;
        }
    }
    return 0;
}

/*

int main()[]
static 
dynamic EBase: [][](hfalse)*(false)( FLOW __false) 
{
{local: int x
int x = (96, ):nondet_int();
 while ((x > 0) && (x < 100)) 
 
{
{local: int old_x
int old_x = x;
x = (99, ):nondet_int();
(100, ):if (x < (2 * old_x) + 10) { 
  (100, ):{(101, ):break };
} else { 
  (100, ):
}}
};
(108, ):return 0}
}

*/
