#!/bin/bash
echo "***** OPERATION: Addition ***************"
sh sec_tester.sh op_add
echo "***** OPERATION: Subtraction ************"
sh sec_tester.sh op_sub
echo "***** OPERATION: Multiplication *********"
sh sec_tester.sh op_mul
echo "***** OPERATION: Less Than **************"
sh sec_tester.sh op_lt
echo "***** OPERATION: Less Than Equal ********"
sh sec_tester.sh op_lte
echo "***** OPERATION: Greather Than **********"
sh sec_tester.sh op_gt
echo "***** OPERATION: Greater Than Equal *****"
sh sec_tester.sh op_gte
echo "***** OPERATION: Assignment *************"
sh sec_tester.sh op_assign
echo "***** DOUBLE-IF: Information ************"
sh sec_tester.sh double_if
echo "***** DOUBLE-IF: Pure & Information *****"
sh sec_tester.sh precise_double_if
echo "***** SINGLE-IF: Information"
sh sec_tester.sh single_if
echo "***** SINGLE-IF: Pure & Information *****"
sh sec_tester.sh precise_single_if
echo "***** BIND: Get *************************"
sh sec_tester.sh bind_get
echo "***** BIND: Deep Get ********************"
sh sec_tester.sh bind_deep
echo "***** FUNCTION: Pre-condition ***********"
sh sec_tester.sh func_pre
