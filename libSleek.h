/*int process_cmd (env* ; char *)
int flush_env()
*/
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/custom.h>
#include <caml/callback.h>


static bool process_cmd (const char * cmd_string; bool flush_context)
{
	CAMLparam0 () ;
	CAMLlocal2 (ostr,o_flush_context,res) ;
    ostr = caml_copy_string (cmd_string);
	o_flush_context = Val_bool(flush_context);
    value * func = caml_named_value ("sleek_process_cmd") ;
	bool b;
    if (func == NULL) 
		puts ("retrieving sleek_process_cmd failed!") ;
    else 
		{res = caml_callback2 (*func, ostr, o_flush_context) ;
		b = Bool_val(res);}
	CAMLreturn (b) ;
}


static void sleeklib_stop ()
{
	CAMLparam0 () ;
	CAMLlocal2 (u) ;
    value * func = caml_named_value ("sleeklib_stop") ;
	bool b;
    if (func == NULL) 
		puts ("retrieving sleeklib_stop failed!") ;
    else  caml_callback (*func, Val_bool(true));
	CAMLreturn0 ;
}


static void sleeklib_init (const char** flags)
{
	CAMLparam0 () ;
      CAMLlocal3 (oargv) ;
      oargv = caml_alloc_array (caml_copy_string, flags) ;
      value * func = caml_named_value ("sleeklib_init") ;
      if (func == NULL) puts ("sleeklib_init failed!") ;
      else caml_callback (*func, oargv) ;
	CAMLreturn0 ;
}



// DO NOT forget to call :     caml_startup (argv) ; 

/*
  gcc -g -Wall -Wextra  -c libTest.c -o ctemp.o; gcc ocamltemp.o ctemp.o -ldl -lm -L /usr/local/lib/ocaml -lasmrun -o libTest
*/
/*
  ocamlopt -c libTest.ml -o libTest.cmx; ocamlopt -output-obj -o ocamltemp.o libTest.cmx ; 
  gcc -g -Wall -Wextra  -c libTest.c -o ctemp.o; gcc ocamltemp.o ctemp.o -ldl -lm -L /usr/local/lib/ocaml -lasmrun -o libTest
*/