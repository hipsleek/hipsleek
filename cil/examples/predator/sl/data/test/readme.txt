SLS abstraction
===============
    test2.c - infinite loop creating a SLL
                - it plots a heap graph per each iteration
                - thanks to the SLS abstraction, the program reaches its end
                  during the symbolic execution (though it can't happen in real
                  world as long as there is some memory available)
                - junk is properly detected since there is some memory
                  allocated, but nothing is free'd afterwards
                - the function "___sl_summary("...");" is used to capture summary of loop

    test1.c - simple SLL creation/destruction
                - one false alarm caused by the poor support of integral values
                - contributed by Petr Peringer
                - the function "___sl_summary("...");" is used to capture summary of each segment of code

