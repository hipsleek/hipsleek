%{
#include <stdio.h>
%}

%%
stop    {printf("Stop command received\n");fflush(stdout);}
start   printf("Start command received\n");
%%
int main ()
{
  yyin = stdin;
  yylex();
  
  return 0;
}