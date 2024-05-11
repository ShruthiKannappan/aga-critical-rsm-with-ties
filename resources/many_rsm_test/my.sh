#!/bin/bash

counter=0

for i in {20..160..10}; do
    for ((j=10; j<(i/10)*10; j+=10)); do
        ./a.out $i $j > "input/input_${counter}.txt"
        ((counter++))
    done
done
