  #include <stdio.h>
  #include <stdlib.h>
  #include <string.h>
  #include <libSleek.h>
  
int main (int argc, char ** argv)
  {  
	  caml_startup (argv) ;        
	  sleeklib_init(argv) ;
	  printf("res: %d \n",process_cmd ("checkentail a>2|-a>1.",1));
	  sleeklib_stop();
      return 0 ;
  } /* main */
 
/*
  ocamlopt -c libTest.ml -o libTest.cmx; ocamlopt -output-obj -o ocamltemp.o libTest.cmx ; 
  gcc -g -Wall -Wextra -I. -c sleekLibUsage.c -o sleekLibUsage.o; 
  gcc sleekLibUsage.o libSleek.o -ldl -lm -L /usr/local/lib/ocaml -lasmrun -o SleekTest
*/
