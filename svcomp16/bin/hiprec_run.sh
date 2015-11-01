
timeout 200 ./hiprec $1
if [ $? -eq 124 ]; then
    printf "Verification result: (UNKNOWN, witness: , 200(seconds))\n"
else
    printf ""
  fi