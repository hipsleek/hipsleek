
int process_cmd (const char * cmd_string, int flush_context);

void sleeklib_stop ();


void sleeklib_init (const char** flags);


// DO NOT forget to call :     caml_startup (argv) ; 

/*
  gcc -g -Wall -Wextra  -c libTest.c -o ctemp.o; gcc ocamltemp.o ctemp.o -ldl -lm -L /usr/local/lib/ocaml -lasmrun -o libTest
*/
/*
  ocamlopt -c libTest.ml -o libTest.cmx; ocamlopt -output-obj -o ocamltemp.o libTest.cmx ; 
  gcc -g -Wall -Wextra  -c libTest.c -o ctemp.o; gcc ocamltemp.o ctemp.o -ldl -lm -L /usr/local/lib/ocaml -lasmrun -o libTest
*/