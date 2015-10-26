extern void __VERIFIER_error() __attribute__ ((__noreturn__));

/*
 * recHanoi.c
 *
 *  Created on: 17.07.2013
 *      Author: Stefan Wissert
 */

extern int __VERIFIER_nondet_int(void);

int counter;


int incr()
{
  counter++;
  return counter;
}

int main() {
    int  result;
    counter = 0;
    result = incr();
    if (result == counter) {
        return 0;
    } else {
        ERROR: __VERIFIER_error();
    }
}



