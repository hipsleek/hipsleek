#!/usr/bin/python
import math

N = 20

def f(x):
  y = x*x - 2
  return y
  
x = 2.1;
fixpoint = 2.0

for i in range(N):
  # print distance 
  #distance = abs(x - fixpoint)
  #print distance
  
  # print value
  print x
  
  # update new value
  x = f(x)

